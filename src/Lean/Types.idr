||| Representation inference: decide which variables, parameters and return
||| values can be unboxed C scalars, then insert box/unbox coercions.
|||
||| Within a function variables are partitioned into classes (union-find) of
||| values that must share a representation (returned values, join point
||| arguments).  A class becomes scalar if any member is produced or consumed
||| by a primitive with a scalar type.  Across functions, information only
||| flows from a callee's signature to its callers (a parameter used as an Int
||| by the callee is an Int at every call site), never backwards, so
||| polymorphic functions stay boxed.  Any assignment is safe: coercions are
||| inserted at every boundary where representations differ.
module Lean.Types

import Core.Name
import Lean.IR
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

public export
data Lat = Unk | Sc Ty | Conflict

export
Eq Lat where
  Unk == Unk = True
  Sc a == Sc b = a == b
  Conflict == Conflict = True
  _ == _ = False

joinLat : Lat -> Lat -> Lat
joinLat Unk x = x
joinLat x Unk = x
joinLat (Sc a) (Sc b) = if a == b then Sc a else Conflict
joinLat _ _ = Conflict

latTy : Lat -> Ty
latTy (Sc t) = t
latTy _ = TObj

public export
record Sig where
  constructor MkSig
  params : List Lat
  ret : Lat

export
Eq Sig where
  a == b = a.params == b.params && a.ret == b.ret

------------------------------------------------------------------------
-- Inference
--
-- Soundness under dependent types: a function may return values of
-- different types in different branches (e.g. `f : (a : Type) -> a` by
-- type-case), so we never unify the representations of different values.
--  * declared functions: parameter/result representations come from their
--    (normalised) types -- scalar only for primitive and enumeration types
--  * local variables: decided by their defining expression (forward)
--  * join point parameters: join of the arguments jumped with
--  * generated functions (lifted lambdas): parameters from their direct uses,
--    with conflicts (scalar vs. definitely-object use) falling back to boxed;
--    results from the join of returned values

||| Lattice element for a semantic "object" use (string, Integer, data...)
ObjF : Lat
ObjF = Conflict

export
litTy : Lit -> Ty
litTy (LInt _ t) = t
litTy (LDouble _) = TF64
litTy _ = TObj

repLat : Ty -> Lat
repLat t = if isScalar t then Sc t else Conflict

||| Natural representation of an expression given the current local reps
exprRep : SortedMap Name Sig -> SortedMap Var Lat -> Expr -> Lat
exprRep sigs loc (EPrim sig _) = repLat sig.ret
exprRep sigs loc (ELit l) = repLat (litTy l)
exprRep sigs loc (ESProj _ t _) = Sc t
exprRep sigs loc (EFap g _) = maybe Unk ret (lookup g sigs)
exprRep sigs loc (ECopy y) = fromMaybe Unk (lookup y loc)
exprRep sigs loc _ = Conflict

record LState where
  constructor MkLState
  loc : SortedMap Var Lat
  jpArgs : SortedMap Int (List Lat)
  rets : Lat

joinArgs : List Lat -> List Lat -> List Lat
joinArgs [] ys = ys
joinArgs xs [] = xs
joinArgs (x :: xs) (y :: ys) = joinLat x y :: joinArgs xs ys

argLat : SortedMap Var Lat -> Arg -> Lat
argLat loc (AVar v) = fromMaybe Unk (lookup v loc)
argLat loc AIrr = Unk

||| Forward computation of local representations
fwd : SortedMap Name Sig -> Body -> State LState ()
fwd sigs (BLet x _ e b) =
  do st <- get
     put ({ loc $= insert x (exprRep sigs st.loc e) } st)
     fwd sigs b
fwd sigs (BJp j ps jb rest) =
  do fwd sigs rest
     st <- get
     let args = fromMaybe [] (lookup j st.jpArgs)
     let pl = map (\(p, i) => case drop i args of
                                 (l :: _) => l
                                 [] => Unk) (zip ps [0 .. length ps])
     put ({ loc $= \m => foldl (\m, (p, l) => insert p.pvar l m) m (zip ps pl) } st)
     fwd sigs jb
fwd sigs (BCase _ _ alts) = traverse_ (fwd sigs . altBody) alts
fwd sigs (BRet a) = modify (\st => { rets $= joinLat (argLat st.loc a) } st)
fwd sigs (BJmp j as) =
  modify (\st => { jpArgs $= \m => insert j (joinArgs (fromMaybe [] (lookup j m)) (map (argLat st.loc) as)) m } st)
fwd sigs _ = pure ()

||| Facts about parameters from their direct uses
useFacts : SortedMap Name Sig -> SortedSet Var -> Body -> List (Var, Lat)
useFacts sigs ps (BLet _ _ e b) = here e ++ useFacts sigs ps b
  where
    onArgs : List Arg -> List Lat -> List (Var, Lat)
    onArgs as ls = mapMaybe (\(a, l) => case a of
                                          AVar v => if contains v ps then Just (v, l) else Nothing
                                          AIrr => Nothing) (zip as ls)
    here : Expr -> List (Var, Lat)
    here (EPrim sig as) = onArgs as (map (\(t, _) => repLat t) sig.params)
    here (EFap g as) = case lookup g sigs of
                         Just s => onArgs as (map (\l => case l of
                                                             Sc t => Sc t
                                                             _ => Unk) s.params)
                         Nothing => []
    here (ECtor c as) = onArgs as (map (\f => case f of
                                                 Right (_, t) => Sc t
                                                 Left _ => Unk) c.fields)
    here _ = []
useFacts sigs ps (BJp _ _ jb r) = useFacts sigs ps jb ++ useFacts sigs ps r
useFacts sigs ps (BCase x ty alts) =
  (if contains x ps then [(x, case alts of
                                (ACtor _ _ :: _) => ObjF
                                _ => repLat ty)] else [])
  ++ concatMap (useFacts sigs ps . altBody) alts
useFacts sigs ps _ = []

||| Declared representations: Nothing = to be inferred
public export
Declared : Type
Declared = SortedMap Name (List (Maybe Ty), Maybe Ty)

isForeign : Decl -> Bool
isForeign d = case d.kind of
                Foreign _ _ _ => True
                _ => False

declSig : Declared -> SortedMap Name Sig -> Decl -> Sig
declSig declared sigs d =
  if isForeign d
     then MkSig (map (repLat . pty) d.params) (repLat d.ret)
     else
       let (dps, dret) = fromMaybe (map (const Nothing) d.params, Nothing) (lookup d.name declared)
           cur = fromMaybe (MkSig (map (const Unk) d.params) Unk) (lookup d.name sigs)
           st = execState (MkLState (fromList (zip (map pvar d.params) cur.params)) empty Unk) (fwd sigs d.body)
           facts = useFacts sigs (fromList (map pvar d.params)) d.body
           pl = map (\(p, dp) => case dp of
                                    Just t => repLat t
                                    Nothing => foldl (\acc, (v, l) => if v == p.pvar then joinLat acc l else acc) Unk facts)
                    (zip d.params (dps ++ replicate (length d.params) Nothing))
           rl = case dret of
                  Just t => repLat t
                  Nothing => st.rets
       in MkSig pl rl

||| Whole-program fixpoint
export
inferSigs : Declared -> List Decl -> SortedMap Name Sig
inferSigs declared ds = go 0 (fromList (map (\d => (d.name, MkSig (map (const Unk) d.params) Unk)) ds))
  where
    step : SortedMap Name Sig -> (SortedMap Name Sig, Bool)
    step sigs = foldl (\(s, ch), d =>
                         let new = declSig declared s d in
                         case lookup d.name s of
                           Just old => if old == new then (s, ch) else (insert d.name new s, True)
                           Nothing => (insert d.name new s, True)) (sigs, False) ds

    go : Nat -> SortedMap Name Sig -> SortedMap Name Sig
    go n sigs = let (sigs', changed) = step sigs in
                if changed && n < 100 then go (S n) sigs' else sigs'

------------------------------------------------------------------------
-- Coercion insertion

record RW where
  constructor MkRW
  next : Int
  boxedOf : SortedMap Var Var   -- scalar var -> object it was unboxed from

freshV : State RW Var
freshV = do s <- get
            put ({ next $= (+1) } s)
            pure s.next

recordBox : Var -> Var -> State RW ()
recordBox x orig = modify ({ boxedOf $= insert x orig })

conv : Ty -> Ty -> Var -> Expr
conv from to v =
  if from == to then ECopy v
  else if isObj to || to == TIrr then (if isScalar from then EBox from v else ECopy v)
  else if isObj from || from == TIrr then EUnbox to v
  else ECast to v

zeroLit : Ty -> Lit
zeroLit TF64 = LDouble 0
zeroLit t = LInt 0 t

||| Coerce an argument to the expected type, returning bindings to prepend
coerceArg : (Var -> Ty) -> Ty -> Arg -> State RW (List (Var, Ty, Expr), Arg)
coerceArg vt TIrr a = pure ([], AIrr)
coerceArg vt want AIrr =
  if isScalar want
     then do y <- freshV
             pure ([(y, want, ELit (zeroLit want))], AVar y)
     else pure ([], AIrr)
coerceArg vt want (AVar v) =
  let have = vt v in
  if have == want then pure ([], AVar v)
  else do st <- get
          case (isObj want, lookup v st.boxedOf) of
            (True, Just orig) => pure ([], AVar orig)
            _ => do y <- freshV
                    when (isObj have && isScalar want) $ recordBox y v
                    pure ([(y, want, conv have want v)], AVar y)

coerceArgs : (Var -> Ty) -> List Ty -> List Arg -> State RW (List (Var, Ty, Expr), List Arg)
coerceArgs vt (t :: ts) (a :: as) =
  do (p1, a') <- coerceArg vt t a
     (p2, as') <- coerceArgs vt ts as
     pure (p1 ++ p2, a' :: as')
coerceArgs vt [] as = pure ([], as)  -- should not happen
coerceArgs vt _ [] = pure ([], [])

prependLets : List (Var, Ty, Expr) -> Body -> Body
prependLets ps b = foldr (\(v, t, e), acc => BLet v t e acc) b ps

objs : List a -> List Ty
objs xs = map (const TObj) xs

record Ctx where
  constructor MkCtx
  vt : Var -> Ty
  sigTy : Name -> Maybe (List Ty, Ty)
  retTy : Ty

||| Coerce the arguments of an expression; return its natural result type
rwExpr : Ctx -> Expr -> State RW (List (Var, Ty, Expr), Expr, Ty)
rwExpr ctx (ECtor c as) = do (p, as') <- coerceArgs ctx.vt (map fieldTy c.fields) as
                             pure (p, ECtor c as', TObj)
  where
    fieldTy : Either Nat (Nat, Ty) -> Ty
    fieldTy (Left _) = TObj
    fieldTy (Right (_, t)) = t
rwExpr ctx (EPap f as) = do (p, as') <- coerceArgs ctx.vt (objs as) as
                            pure (p, EPap f as', TObj)
rwExpr ctx (EAp f as) = do (p, as') <- coerceArgs ctx.vt (objs as) as
                           (pf, f') <- coerceArg ctx.vt TObj (AVar f)
                           case f' of
                             AVar fv => pure (pf ++ p, EAp fv as', TObj)
                             AIrr => pure (pf ++ p, EAp f as', TObj)
rwExpr ctx (EFap g as) =
  case ctx.sigTy g of
    Just (pts, r) => do (p, as') <- coerceArgs ctx.vt pts as
                        pure (p, EFap g as', r)
    Nothing => pure ([], EFap g as, TObj)
rwExpr ctx (EPrim sig as) = do (p, as') <- coerceArgs ctx.vt (map fst sig.params) as
                               pure (p, EPrim sig as', sig.ret)
rwExpr ctx (ELit l) = pure ([], ELit l, litTy l)
rwExpr ctx (ECopy v) = pure ([], ECopy v, ctx.vt v)
rwExpr ctx (EProj i x) = pure ([], EProj i x, TObj)
rwExpr ctx (ESProj o t x) = pure ([], ESProj o t x, t)
rwExpr ctx e = pure ([], e, TObj)

rw : Ctx -> SortedMap Int (List Ty) -> Body -> State RW Body
rw ctx jps (BLet x _ e b) =
  do (pre, e', nat) <- rwExpr ctx e
     let want = ctx.vt x
     case e' of
       ECopy v => do when (isObj nat && isScalar want) $ recordBox x v
                     b' <- rw ctx jps b
                     pure (prependLets pre (BLet x want (conv nat want v) b'))
       _ => if nat == want || want == TIrr
               then do b' <- rw ctx jps b
                       pure (prependLets pre (BLet x nat e' b'))
               else do y <- freshV
                       when (isObj nat && isScalar want) $ recordBox x y
                       b' <- rw ctx jps b
                       pure (prependLets pre (BLet y nat e' (BLet x want (conv nat want y) b')))
rw ctx jps (BJp j ps jb rest) =
  do let ps' = map (\p => { pty := ctx.vt p.pvar } p) ps
     jb' <- rw ctx jps jb
     rest' <- rw ctx (insert j (map pty ps') jps) rest
     pure (BJp j ps' jb' rest')
rw ctx jps (BCase x ty alts) =
  do let want = case alts of
                  (ACtor _ _ :: _) => TObj
                  _ => ty
     (pre, x') <- coerceArg ctx.vt want (AVar x)
     alts' <- traverse (\a => setAltBody a <$> rw ctx jps (altBody a)) alts
     case x' of
       AVar xv => pure (prependLets pre (BCase xv want alts'))
       AIrr => pure (prependLets pre (BCase x want alts'))
rw ctx jps (BRet a) =
  do (pre, a') <- coerceArg ctx.vt ctx.retTy a
     pure (prependLets pre (BRet a'))
rw ctx jps (BJmp j as) =
  do let ts = fromMaybe (objs as) (lookup j jps)
     (pre, as') <- coerceArgs ctx.vt ts as
     pure (prependLets pre (BJmp j as'))
rw ctx jps b = pure b

maxVarB : Body -> Int
maxVarB (BLet x _ _ b) = max x (maxVarB b)
maxVarB (BJp _ ps jb r) = foldl max (max (maxVarB jb) (maxVarB r)) (map pvar ps)
maxVarB (BCase x _ alts) = foldl max x (map (maxVarB . altBody) alts)
maxVarB (BRet (AVar x)) = x
maxVarB _ = 0

export
applyTypes : SortedMap Name Sig -> Decl -> Decl
applyTypes sigs d =
  if isForeign d then d else
  let sig = fromMaybe (MkSig (map (const Unk) d.params) Unk) (lookup d.name sigs)
      st = execState (MkLState (fromList (zip (map pvar d.params) sig.params)) empty Unk) (fwd sigs d.body)
      vt : Var -> Ty
      vt v = latTy (fromMaybe Unk (lookup v st.loc))
      sigTy : Name -> Maybe (List Ty, Ty)
      sigTy g = map (\s => (map latTy s.params, latTy s.ret)) (lookup g sigs)
      ret = latTy sig.ret
      ctx = MkCtx vt sigTy ret
      start = foldl max (maxVarB d.body) (map pvar d.params) + 1
      body' = evalState (MkRW start empty) (rw ctx empty d.body)
  in { params := map (\p => { pty := vt p.pvar } p) d.params,
       ret := ret,
       body := body' } d
