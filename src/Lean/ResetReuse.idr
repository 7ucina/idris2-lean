||| Insertion of reset/reuse instructions (functions R, D and S of "Counting
||| Immutable Beans"; port of Lean 4's ResetReuse pass).
|||
||| When a constructor value `x` is matched and dead after some point, and a
||| constructor of the same shape is allocated afterwards, we `reset` x and
||| `reuse` its memory cell for the new allocation.
module Lean.ResetReuse

import Core.Name
import Lean.IR
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

mayReuse : CtorInfo -> CtorInfo -> Bool
mayReuse c1 c2 = c1.size == c2.size && c1.ssize == c2.ssize

record Ctx where
  constructor MkCtx
  jps : SortedMap Int (SortedSet Var)   -- free variables of join points in scope
  alreadyFound : SortedSet Var

M : Type -> Type
M = State Int

freshV : M Var
freshV = do n <- get
            put (n + 1)
            pure n

live : Ctx -> Var -> Body -> Bool
live ctx x b = contains x (freeVars ctx.jps b)

||| S: replace a compatible allocation by a reuse of w.  Returns whether a
||| replacement happened.
sReplace : Var -> CtorInfo -> Body -> (Body, Bool)
sReplace w c (BLet x t (ECtor c' ys) b) =
  if mayReuse c c' && not (isScalarCtor c')
     then (BLet x t (EReuse w c' (c.tag /= c'.tag) ys) b, True)
     else let (b', ch) = sReplace w c b in (BLet x t (ECtor c' ys) b', ch)
sReplace w c (BLet x t e b) = let (b', ch) = sReplace w c b in (BLet x t e b', ch)
sReplace w c (BJp j ps jb r) =
  let (jb', ch) = sReplace w c jb in
  if ch then (BJp j ps jb' r, True)
  else let (r', ch') = sReplace w c r in (BJp j ps jb r', ch')
sReplace w c (BCase x ty alts) =
  let rs = map (\a => let (b, ch) = sReplace w c (altBody a) in (setAltBody a b, ch)) alts
  in (BCase x ty (map fst rs), any snd rs)
sReplace w c b = (b, False)

tryS : Var -> CtorInfo -> Body -> M Body
tryS x c b =
  do w <- freshV
     let (b', ch) = sReplace w c b
     pure (if ch then BLet w TObj (EReset c.size x) b' else b)

isCtorUsing : Expr -> Var -> Bool
isCtorUsing (ECtor _ ys) x = AVar x `elem` ys
isCtorUsing _ _ = False

mutual
  ||| Dmain: returns the new body and whether x is live in it
  dmain : Ctx -> Var -> CtorInfo -> Body -> M (Body, Bool)
  dmain ctx x c b@(BCase y ty alts) =
    if live ctx x b
       then do alts' <- traverse (\a => setAltBody a <$> d ctx x c (altBody a)) alts
               pure (BCase y ty alts', True)
       else pure (b, False)
  dmain ctx x c (BJp j ps jb r) =
    do let jfv = foldl (\s, p => delete p.pvar s) (freeVars ctx.jps jb) ps
       (r', found) <- dmain ({ jps $= insert j jfv } ctx) x c r
       (jb', _) <- dmain ctx x c jb
       pure (BJp j ps jb' r', found)
  dmain ctx x c b@(BLet z t e rest) =
    if isCtorUsing e x then pure (b, True)
    else do (rest', found) <- dmain ctx x c rest
            if found || not (x `elem` exprVars e)
               then pure (BLet z t e rest', found)
               else do rest'' <- tryS x c rest'
                       pure (BLet z t e rest'', True)
  dmain ctx x c b = pure (b, live ctx x b)

  d : Ctx -> Var -> CtorInfo -> Body -> M Body
  d ctx x c b = do (b', found) <- dmain ctx x c b
                   if found then pure b' else tryS x c b'

r : Ctx -> Body -> M Body
r ctx (BCase x ty alts) =
  do let already = contains x ctx.alreadyFound
     let ctx' = { alreadyFound $= insert x } ctx
     alts' <- traverse (\a => do b <- r ctx' (altBody a)
                                 case a of
                                   ACtor c _ =>
                                     if isScalarCtor c || already
                                        then pure (ACtor c b)
                                        else ACtor c <$> d ctx' x c b
                                   _ => pure (setAltBody a b)) alts
     pure (BCase x ty alts')
r ctx (BJp j ps jb rest) =
  do jb' <- r ctx jb
     let jfv = foldl (\s, p => delete p.pvar s) (freeVars ctx.jps jb') ps
     rest' <- r ({ jps $= insert j jfv } ctx) rest
     pure (BJp j ps jb' rest')
r ctx (BLet z t e b) = BLet z t e <$> r ctx b
r ctx b = pure b

maxVarB : Body -> Int
maxVarB (BLet x _ _ b) = max x (maxVarB b)
maxVarB (BJp _ ps jb r) = foldl max (max (maxVarB jb) (maxVarB r)) (map pvar ps)
maxVarB (BCase x _ alts) = foldl max x (map (maxVarB . altBody) alts)
maxVarB (BRet (AVar x)) = x
maxVarB _ = 0

export
insertResetReuse : Decl -> Decl
insertResetReuse dcl =
  case dcl.kind of
    Normal =>
      let start = foldl max (maxVarB dcl.body) (map pvar dcl.params) + 1
      in { body := evalState start (r (MkCtx empty empty) dcl.body) } dcl
    _ => dcl
