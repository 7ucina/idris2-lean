||| Simple IR optimisations: dead let elimination and floating pure lets into
||| the (single) case branch that uses them (like Lean's floatLetIn/pushProj).
module Lean.Opt

import Core.Name
import Lean.IR
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

||| Expressions without side effects (may be removed if unused, or moved)
export
isPure : Expr -> Bool
isPure (ECtor _ _) = True
isPure (EProj _ _) = True
isPure (ESProj _ _ _) = True
isPure (EPap _ _) = True
isPure (EBox _ _) = True
isPure (EUnbox _ _) = True
isPure (ELit _) = True
isPure (ECast _ _) = True
isPure (ECopy _) = True
isPure (EPrim sig _) = sig.pure_
isPure (EIsShared _) = True
isPure _ = False

||| Expressions worth moving into branches
movable : Expr -> Bool
movable (EPrim _ _) = False   -- keep arithmetic where it is
movable e = isPure e

fv : Body -> SortedSet Var
fv = freeVars empty

mutual
  ||| Remove unused pure lets.  Returns the body and its free variables.
  dce : Body -> (Body, SortedSet Var)
  dce (BLet x t e b) =
    let (b', s) = dce b in
    if not (contains x s) && isPure e then (b', s)
    else (BLet x t e b', delete x s `union` fromList (exprVars e))
  dce (BJp j ps jb rest) =
    let (jb', s1) = dce jb
        (rest', s2) = dce rest
        s1' = foldl (\s, p => delete p.pvar s) s1 ps
    in (BJp j ps jb' rest', s1' `union` s2)
  dce (BCase x ty alts) =
    let rs = map (\a => let (b, s) = dce (altBody a) in (setAltBody a b, s)) alts
    in (BCase x ty (map fst rs), insert x (foldl union empty (map snd rs)))
  dce b@(BRet (AVar x)) = (b, singleton x)
  dce b@(BJmp _ as) = (b, fromList (argVars as))
  dce b = (b, empty)

-- Note: dce treats join point free variables locally (the jp's own free
-- variables are included at the BJp), which is a safe over-approximation.

||| Push `let x = e` (pure) as deep as possible
push : Var -> Ty -> Expr -> Body -> Body
push x t e b@(BLet y t2 e2 b2) =
  -- Projections are never moved past other instructions: that would extend
  -- the lifetime of the scrutinee and prevent reset/reuse.
  if isProj e || contains x (fromList (exprVars e2)) then BLet x t e b
  else BLet y t2 e2 (push x t e b2)
  where
    isProj : Expr -> Bool
    isProj (EProj _ _) = True
    isProj (ESProj _ _ _) = True
    isProj _ = False
push x t e b@(BCase s ty alts) =
  if s == x then BLet x t e b
  else let users = filter (\a => contains x (fv (altBody a))) alts in
       case users of
         [] => b
         [_] => BCase s ty (map (\a => if contains x (fv (altBody a)) then setAltBody a (push x t e (altBody a)) else a) alts)
         _ => BLet x t e b
push x t e b@(BJp j ps jb r) =
  let inJb = contains x (fv jb)
      inR = contains x (fv r) in
  if not inJb then BJp j ps jb (push x t e r)
  else if not inR then BJp j ps (push x t e jb) r
  else BLet x t e b
push x t e b = BLet x t e b

export
floatLets : Body -> Body
floatLets (BLet x t e b) =
  let b' = floatLets b in
  if movable e then push x t e b' else BLet x t e b'
floatLets (BJp j ps jb r) = BJp j ps (floatLets jb) (floatLets r)
floatLets (BCase x ty alts) = BCase x ty (map (\a => setAltBody a (floatLets (altBody a))) alts)
floatLets b = b

export
simplify : Decl -> Decl
simplify d = case d.kind of
  Normal => { body := fst (dce (floatLets (fst (dce d.body)))) } d
  _ => d
