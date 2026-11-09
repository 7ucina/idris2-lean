||| Expansion of reset/reuse (port of Lean 4's ExpandResetReuse) and a small
||| peephole pass cancelling `inc x ... dec x` pairs.
|||
|||   let w = reset[n] y; b
||| becomes
|||   if isShared y then (inc moved fields; dec y; b[reuse w -> ctor])
|||   else (release fields not moved; b[reuse w -> in place update of y])
|||
||| In the fast path the increments of projected fields are not needed (the
||| fields are moved out of the cell), and stores of unchanged fields are removed.
module Lean.Expand

import Core.Name
import Lean.IR
import Lean.Opt
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

------------------------------------------------------------------------
-- Instructions (non-branching body prefixes)

data Instr = ILet Var Ty Expr
           | IInc Var Nat
           | IDec Var
           | IDel Var
           | ISetTag Var Int
           | ISet Var Nat Arg
           | ISSet Var Nat Nat Ty Var
           | IRelease Var Nat

split : Body -> Maybe (Instr, Body)
split (BLet x t e b) = Just (ILet x t e, b)
split (BInc x n b) = Just (IInc x n, b)
split (BDec x b) = Just (IDec x, b)
split (BDel x b) = Just (IDel x, b)
split (BSetTag x t b) = Just (ISetTag x t, b)
split (BSet x i a b) = Just (ISet x i a, b)
split (BSSet x n o t y b) = Just (ISSet x n o t y, b)
split (BRelease x i b) = Just (IRelease x i, b)
split _ = Nothing

setBody : Instr -> Body -> Body
setBody (ILet x t e) b = BLet x t e b
setBody (IInc x n) b = BInc x n b
setBody (IDec x) b = BDec x b
setBody (IDel x) b = BDel x b
setBody (ISetTag x t) b = BSetTag x t b
setBody (ISet x i a) b = BSet x i a b
setBody (ISSet x n o t y) b = BSSet x n o t y b
setBody (IRelease x i) b = BRelease x i b

||| bs is in reverse order (head = last instruction)
reshape : List Instr -> Body -> Body
reshape bs b = foldl (\acc, i => setBody i acc) b bs

------------------------------------------------------------------------
-- Substitution and renaming

substArg : Var -> Var -> Arg -> Arg
substArg x y (AVar v) = AVar (if v == x then y else v)
substArg x y AIrr = AIrr

substExpr : Var -> Var -> Expr -> Expr
substExpr x y e =
  let s : Var -> Var
      s v = if v == x then y else v
      sa : List Arg -> List Arg
      sa = map (substArg x y) in
  case e of
    ECtor c as => ECtor c (sa as)
    EReset n v => EReset n (s v)
    EReuse w c u as => EReuse (s w) c u (sa as)
    EProj i v => EProj i (s v)
    ESProj o t v => ESProj o t (s v)
    EFap f as => EFap f (sa as)
    EPap f as => EPap f (sa as)
    EAp f as => EAp (s f) (sa as)
    EBox t v => EBox t (s v)
    EUnbox t v => EUnbox t (s v)
    ELit l => ELit l
    EPrim p as => EPrim p (sa as)
    ECast t v => ECast t (s v)
    EIsShared v => EIsShared (s v)
    ECopy v => ECopy (s v)

||| substitute variable x by y (x is not rebound inside)
subst : Var -> Var -> Body -> Body
subst x y b =
  let s : Var -> Var
      s v = if v == x then y else v in
  case b of
    BLet z t e k => BLet z t (substExpr x y e) (subst x y k)
    BJp j ps jb r => BJp j ps (subst x y jb) (subst x y r)
    BCase v t alts => BCase (s v) t (map (\a => setAltBody a (subst x y (altBody a))) alts)
    BRet a => BRet (substArg x y a)
    BJmp j as => BJmp j (map (substArg x y) as)
    BUnreach m => BUnreach m
    BInc v n k => BInc (s v) n (subst x y k)
    BDec v k => BDec (s v) (subst x y k)
    BDel v k => BDel (s v) (subst x y k)
    BSetTag v t k => BSetTag (s v) t (subst x y k)
    BSet v i a k => BSet (s v) i (substArg x y a) (subst x y k)
    BSSet v n o t w k => BSSet (s v) n o t (s w) (subst x y k)
    BRelease v i k => BRelease (s v) i (subst x y k)

record ES where
  constructor MkES
  nextVar : Int
  nextJp : Int

M : Type -> Type
M = State ES

freshV : M Var
freshV = do s <- get
            put ({ nextVar $= (+1) } s)
            pure s.nextVar

freshJ : M Int
freshJ = do s <- get
            put ({ nextJp $= (+1) } s)
            pure s.nextJp

||| Give all join points in a body fresh ids (used when duplicating code)
freshenJps : SortedMap Int Int -> Body -> M Body
freshenJps m (BJp j ps jb r) =
  do j' <- freshJ
     jb' <- freshenJps m jb
     r' <- freshenJps (insert j j' m) r
     pure (BJp j' ps jb' r')
freshenJps m (BJmp j as) = pure (BJmp (fromMaybe j (lookup j m)) as)
freshenJps m (BCase x t alts) = BCase x t <$> traverse (\a => setAltBody a <$> freshenJps m (altBody a)) alts
freshenJps m b = case split b of
                   Just (i, k) => setBody i <$> freshenJps m k
                   Nothing => pure b

------------------------------------------------------------------------
-- Expansion

consumed : Var -> Body -> Bool
consumed x (BLet _ _ (EReuse y _ _ _) b) = x == y || consumed x b
consumed x (BDec y b) = x == y || consumed x b
consumed x (BCase _ _ alts) = all (consumed x . altBody) alts
consumed x (BJp _ _ _ r) = consumed x r
consumed x b = case split b of
                 Just (_, k) => consumed x k
                 Nothing => False

||| instructions that can be skipped while looking for projection increments
harmless : Instr -> Bool
harmless (ILet _ _ (ESProj _ _ _)) = True
harmless (ILet _ _ (EUnbox _ _)) = True
harmless (ILet _ _ (ELit _)) = True
harmless (ILet _ t (EPrim sig _)) = sig.pure_ && all (\(ty, b) => b || not (isObj ty)) sig.params && not (isObj t)
harmless (ILet _ _ (ECast _ _)) = True
harmless _ = False

||| Erase `let z = proj[i] y; inc z` pairs before a reset of y.
||| Returns the remaining instructions (reversed) and the mask.
eraseProjIncFor : Nat -> Var -> List Instr -> (List Instr, List (Maybe Var))
eraseProjIncFor n y bs = go bs (replicate n Nothing) []
  where
    setAt : Nat -> Var -> List (Maybe Var) -> List (Maybe Var)
    setAt i z xs = zipWith (\k, m => if k == i then Just z else m) [0 .. length xs] xs

    go : List Instr -> List (Maybe Var) -> List Instr -> (List Instr, List (Maybe Var))
    go (i@(IInc z k) :: p@(ILet w t (EProj idx v)) :: rest) mask keep =
      if w == z && v == y && idx < n && isNothing (join (head' (drop idx mask)))
         then let keep' = (if k == 1 then [] else [IInc z (minus k 1)]) ++ (p :: keep)
              in go rest (setAt idx z mask) keep'
         else (reverse keep ++ (i :: p :: rest), mask)
    go (i :: rest) mask keep =
      if harmless i then go rest mask (i :: keep)
      else (reverse keep ++ (i :: rest), mask)
    go [] mask keep = (reverse keep, mask)

reuseToCtor : Var -> Body -> Body
reuseToCtor x (BDec y b) = if x == y then b else BDec y (reuseToCtor x b)
reuseToCtor x (BLet z t (EReuse y c _ zs) b) =
  if x == y then BLet z t (ECtor c zs) b else BLet z t (EReuse y c False zs) (reuseToCtor x b)
reuseToCtor x (BCase y t alts) = BCase y t (map (\a => setAltBody a (reuseToCtor x (altBody a))) alts)
reuseToCtor x (BJp j ps jb r) = BJp j ps (reuseToCtor x jb) (reuseToCtor x r)
reuseToCtor x b = case split b of
                    Just (i, k) => setBody i (reuseToCtor x k)
                    Nothing => b

mkSlowPath : Var -> Var -> List (Maybe Var) -> Body -> Body
mkSlowPath x y mask b =
  let b1 = BDec y (reuseToCtor x b)
  in foldl (\acc, m => case m of
                         Just z => BInc z 1 acc
                         Nothing => acc) b1 mask

||| projections: var -> (Left boxed index | Right scalar offset, parent)
ProjMap : Type
ProjMap = SortedMap Var (Either Nat Nat, Var)

isSelfSet : ProjMap -> Var -> Nat -> Arg -> Bool
isSelfSet pm y i (AVar z) = lookup z pm == Just (Left i, y)
isSelfSet _ _ _ _ = False

removeSelfSet : ProjMap -> Body -> Body
removeSelfSet pm (BSet y i a b) =
  if isSelfSet pm y i a then removeSelfSet pm b else BSet y i a (removeSelfSet pm b)
removeSelfSet pm (BSSet y n off t z b) =
  if lookup z pm == Just (Right off, y) then removeSelfSet pm b else BSSet y n off t z (removeSelfSet pm b)
removeSelfSet pm b = b

setFields : Var -> CtorInfo -> List Arg -> Body -> Body
setFields y c zs b = foldr set b (zip c.fields zs)
  where
    set : (Either Nat (Nat, Ty), Arg) -> Body -> Body
    set (Left i, z) acc = BSet y i z acc
    set (Right (off, t), AVar z) acc = BSSet y 0 off t z acc
    set (Right _, AIrr) acc = acc

reuseToSet : ProjMap -> Var -> Var -> Body -> Body
reuseToSet pm x y (BDec z b) = if x == z then BDel y b else BDec z (reuseToSet pm x y b)
reuseToSet pm x y (BLet z t (EReuse w c u zs) b) =
  if x == w
     then let b' = setFields y c zs (subst z y b)
              b'' = if u then BSetTag y c.tag b' else b'
          in removeSelfSetPrefix b''
     else BLet z t (EReuse w c u zs) (reuseToSet pm x y b)
  where
    removeSelfSetPrefix : Body -> Body
    removeSelfSetPrefix (BSetTag v t k) = BSetTag v t (removeSelfSet pm k)
    removeSelfSetPrefix k = removeSelfSet pm k
reuseToSet pm x y (BCase z t alts) = BCase z t (map (\a => setAltBody a (reuseToSet pm x y (altBody a))) alts)
reuseToSet pm x y (BJp j ps jb r) = BJp j ps (reuseToSet pm x y jb) (reuseToSet pm x y r)
reuseToSet pm x y b = case split b of
                        Just (i, k) => setBody i (reuseToSet pm x y k)
                        Nothing => b

releaseUnreferencedFields : Var -> List (Maybe Var) -> Body -> M Body
releaseUnreferencedFields y mask b =
  foldlM (\acc, (i, m) => case m of
                            Just _ => pure acc
                            Nothing => do f <- freshV
                                          pure (BLet f TObj (EProj i y) (BDec f acc)))
         b (zip [0 .. length mask] mask)

mutual
  expand : ProjMap -> List Instr -> Var -> Nat -> Var -> Body -> M Body
  expand pm bs x n y b =
    do let (bs', mask) = eraseProjIncFor n y bs
       slow <- freshenJps empty (mkSlowPath x y mask b)
       fast0 <- releaseUnreferencedFields y mask (reuseToSet pm x y b)
       fast <- searchAndExpand pm fast0 []
       c <- freshV
       pure (reshape bs' (BLet c TU8 (EIsShared y)
                           (BCase c TU8 [ALit (LInt 0 TU8) fast, ADefault slow])))

  searchAndExpand : ProjMap -> Body -> List Instr -> M Body
  searchAndExpand pm d@(BLet x t (EReset n y) b) bs =
    if consumed x b then expand pm bs x n y b
    else searchAndExpand pm b (ILet x t (EReset n y) :: bs)
  searchAndExpand pm (BJp j ps jb r) bs =
    do jb' <- searchAndExpand pm jb []
       r' <- searchAndExpand pm r []
       pure (reshape bs (BJp j ps jb' r'))
  searchAndExpand pm (BCase x t alts) bs =
    do alts' <- traverse (\a => setAltBody a <$> searchAndExpand pm (altBody a) []) alts
       pure (reshape bs (BCase x t alts'))
  searchAndExpand pm b bs =
    case split b of
      Just (i, k) => searchAndExpand pm k (i :: bs)
      Nothing => pure (reshape bs b)

projMap : Body -> List (Var, (Either Nat Nat, Var))
projMap (BLet z _ (EProj i y) b) = (z, (Left i, y)) :: projMap b
projMap (BLet z _ (ESProj off _ y) b) = (z, (Right off, y)) :: projMap b
projMap (BJp _ _ jb r) = projMap jb ++ projMap r
projMap (BCase _ _ alts) = concatMap (projMap . altBody) alts
projMap b = case split b of
              Just (_, k) => projMap k
              Nothing => []

maxIds : Body -> (Int, Int)
maxIds (BLet x _ _ b) = let (v, j) = maxIds b in (max x v, j)
maxIds (BJp j ps jb r) =
  let (v1, j1) = maxIds jb
      (v2, j2) = maxIds r in
  (foldl max (max v1 v2) (map pvar ps), max j (max j1 j2))
maxIds (BCase x _ alts) = foldl (\(v, j), a => let (v', j') = maxIds (altBody a) in (max v v', max j j')) (x, 0) alts
maxIds b = case split b of
             Just (_, k) => maxIds k
             Nothing => (0, 0)

export
expandResetReuse : Decl -> Decl
expandResetReuse d =
  case d.kind of
    Normal =>
      let (mv, mj) = maxIds d.body
          start = foldl max mv (map pvar d.params) + 1
          pm = fromList (projMap d.body)
      in { body := evalState (MkES start (mj + 1)) (searchAndExpand pm d.body []) } d
    _ => d

------------------------------------------------------------------------
-- inc/dec cancellation

||| instructions that neither consume nor free objects
transparent : Instr -> Bool
transparent (ILet _ _ (EUnbox _ _)) = True
transparent (ILet _ _ (ESProj _ _ _)) = True
transparent (ILet _ _ (EProj _ _)) = True
transparent (ILet _ _ (ELit _)) = True
transparent (ILet _ _ (EBox _ _)) = True
transparent (ILet _ _ (ECast _ _)) = True
transparent (ILet _ _ (EIsShared _)) = True
transparent (ILet _ t (EPrim sig _)) = sig.pure_ && all snd sig.params
transparent (IInc _ _) = True
transparent _ = False

||| Try to find `dec x` after transparent instructions; remove it
findDec : Var -> Body -> Maybe Body
findDec x (BDec y b) = if x == y then Just b else Nothing
findDec x b = case split b of
                Just (i, k) => if transparent i then setBody i <$> findDec x k else Nothing
                Nothing => Nothing

export
cancelIncDec : Body -> Body
cancelIncDec (BInc x n b) =
  case findDec x b of
    Just b' => cancelIncDec (if n == 1 then b' else BInc x (minus n 1) b')
    Nothing => BInc x n (cancelIncDec b)
cancelIncDec (BJp j ps jb r) = BJp j ps (cancelIncDec jb) (cancelIncDec r)
cancelIncDec (BCase x t alts) = BCase x t (map (\a => setAltBody a (cancelIncDec (altBody a))) alts)
cancelIncDec b = case split b of
                   Just (i, k) => setBody i (cancelIncDec k)
                   Nothing => b
