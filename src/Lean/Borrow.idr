||| Borrowed parameter inference (port of Lean 4's IR Borrow pass).
|||
||| All object parameters (of functions and join points) start out borrowed.
||| A parameter becomes owned when it is reset, stored in a constructor or
||| closure, passed to an owned parameter, applied as a closure, or when
||| owning it is needed to preserve a tail call.  Iterated to a fixpoint.
module Lean.Borrow

import Core.Name
import Lean.IR
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

record BState where
  constructor MkBState
  owned : SortedSet (Name, Var)
  paramMap : SortedMap Name (List Param)
  jpMap : SortedMap (Name, Int) (List Param)
  modified : Bool

record BCtx where
  constructor MkBCtx
  currFn : Name
  paramSet : SortedSet Var

B : Type -> Type
B = State BState

ownVar : BCtx -> Var -> B ()
ownVar ctx x = modify $ \s =>
  if contains (ctx.currFn, x) s.owned then s
  else { owned $= insert (ctx.currFn, x), modified := True } s

ownArg : BCtx -> Arg -> B ()
ownArg ctx (AVar x) = ownVar ctx x
ownArg ctx AIrr = pure ()

isOwned : BCtx -> Var -> B Bool
isOwned ctx x = do s <- get
                   pure (contains (ctx.currFn, x) s.owned)

ownArgsUsingParams : BCtx -> List Arg -> List Param -> B ()
ownArgsUsingParams ctx xs ps =
  traverse_ (\(x, p) => unless p.borrow (ownArg ctx x)) (zip xs ps)

ownParamsUsingArgs : BCtx -> List Arg -> List Param -> B ()
ownParamsUsingArgs ctx xs ps =
  traverse_ (\(x, p) => case x of
                          AVar v => when !(isOwned ctx v) (ownVar ctx p.pvar)
                          AIrr => pure ()) (zip xs ps)

ownArgsIfParam : BCtx -> List Arg -> B ()
ownArgsIfParam ctx xs =
  traverse_ (\x => case x of
                     AVar v => when (contains v ctx.paramSet) (ownVar ctx v)
                     AIrr => pure ()) xs

getParams : Name -> B (Maybe (List Param))
getParams f = do s <- get
                 pure (lookup f s.paramMap)

||| Update a parameter list using the current owned set
updateParams : BCtx -> List Param -> B (List Param)
updateParams ctx ps =
  traverse (\p => if not p.borrow then pure p
                  else do o <- isOwned ctx p.pvar
                          if o then do modify ({ modified := True })
                                       pure ({ borrow := False } p)
                               else pure p) ps

collectExpr : BCtx -> Var -> Expr -> B ()
collectExpr ctx z (EReset _ x) = do ownVar ctx z; ownVar ctx x
collectExpr ctx z (EReuse x _ _ ys) = do ownVar ctx z; ownVar ctx x; ownArgsIfParam ctx ys
collectExpr ctx z (ECtor _ xs) = do ownVar ctx z; ownArgsIfParam ctx xs
collectExpr ctx z (EProj _ x) =
  do when !(isOwned ctx x) (ownVar ctx z)
     when !(isOwned ctx z) (ownVar ctx x)
collectExpr ctx z (EFap g xs) =
  do ownVar ctx z
     Just ps <- getParams g
       | Nothing => traverse_ (ownArg ctx) xs
     ownArgsUsingParams ctx xs ps
collectExpr ctx z (EPrim sig xs) =
  do ownVar ctx z
     traverse_ (\(x, (_, b)) => unless b (ownArg ctx x)) (zip xs sig.params)
collectExpr ctx z (EAp x ys) = do ownVar ctx z; ownVar ctx x; ownArgsIfParam ctx ys
collectExpr ctx z (EPap _ xs) = do ownVar ctx z; ownArgsIfParam ctx xs
collectExpr ctx z (ECopy x) =
  -- z is an alias of x
  do when !(isOwned ctx x) (ownVar ctx z)
     when !(isOwned ctx z) (ownVar ctx x)
collectExpr ctx z _ = pure ()

preserveTailCall : BCtx -> Var -> Expr -> Body -> B ()
preserveTailCall ctx x (EFap g ys) (BRet (AVar z)) =
  when (x == z) $
    do Just ps <- getParams g
         | Nothing => pure ()
       ownParamsUsingArgs ctx ys ps
preserveTailCall _ _ _ _ = pure ()

collectBody : BCtx -> Body -> B ()
collectBody ctx (BJp j ps jb rest) =
  do collectBody ({ paramSet $= \s => foldl (\s, p => insert p.pvar s) s ps } ctx) jb
     s <- get
     let ps0 = fromMaybe ps (lookup (ctx.currFn, j) s.jpMap)
     ps' <- updateParams ctx ps0
     modify ({ jpMap $= insert (ctx.currFn, j) ps' })
     collectBody ctx rest
collectBody ctx (BLet x _ e b) =
  do collectBody ctx b
     collectExpr ctx x e
     preserveTailCall ctx x e b
collectBody ctx (BJmp j ys) =
  do s <- get
     case lookup (ctx.currFn, j) s.jpMap of
       Just ps => do ownArgsUsingParams ctx ys ps
                     ownParamsUsingArgs ctx ys ps
       Nothing => pure ()
collectBody ctx (BCase _ _ alts) = traverse_ (collectBody ctx . altBody) alts
collectBody ctx (BRet (AVar x)) = pure ()
collectBody ctx _ = pure ()

collectDecl : Decl -> B ()
collectDecl d =
  case d.kind of
    Normal =>
      do let ctx = MkBCtx d.name (fromList (map pvar d.params))
         collectBody ctx d.body
         Just ps <- getParams d.name
           | Nothing => pure ()
         ps' <- updateParams ctx ps
         modify ({ paramMap $= insert d.name ps' })
    _ => pure ()

-- initial jp params: borrowed (objects only)
initJps : Name -> Body -> List ((Name, Int), List Param)
initJps f (BJp j ps jb r) = ((f, j), map initP ps) :: initJps f jb ++ initJps f r
  where initP : Param -> Param
        initP p = { borrow := isObj p.pty } p
initJps f (BLet _ _ _ b) = initJps f b
initJps f (BCase _ _ alts) = concatMap (initJps f . altBody) alts
initJps f _ = []

applyJps : SortedMap (Name, Int) (List Param) -> Name -> Body -> Body
applyJps m f (BJp j ps jb r) =
  BJp j (fromMaybe ps (lookup (f, j) m)) (applyJps m f jb) (applyJps m f r)
applyJps m f (BLet x t e b) = BLet x t e (applyJps m f b)
applyJps m f (BCase x t alts) = BCase x t (map (\a => setAltBody a (applyJps m f (altBody a))) alts)
applyJps m f b = b

export
inferBorrow : (exported : Name -> Bool) -> List Decl -> List Decl
inferBorrow exported ds =
  let initParams = fromList (map (\d => (d.name, map (initP d) d.params)) ds)
      initJ = fromList (concatMap (\d => case d.kind of
                                             Normal => initJps d.name d.body
                                             _ => []) ds)
      s = loop 0 (MkBState empty initParams initJ False)
  in map (apply s) ds
  where
    initP : Decl -> Param -> Param
    initP d p = case d.kind of
                  Normal => { borrow := isObj p.pty && not (exported d.name) } p
                  _ => p   -- foreign functions: keep their declared modes

    loop : Nat -> BState -> BState
    loop n s =
      let s' = execState ({ modified := False } s) (traverse_ collectDecl ds) in
      if s'.modified && n < 1000 then loop (S n) s' else s'

    apply : BState -> Decl -> Decl
    apply s d = case d.kind of
                  Normal => { params := fromMaybe d.params (lookup d.name s.paramMap),
                              body := applyJps s.jpMap d.name d.body } d
                  _ => d
