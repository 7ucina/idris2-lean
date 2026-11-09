||| Purity analysis and common subexpression elimination.
|||
||| Idris' ANF threads a single world token through IO code (it is not
||| linear), so two calls with identical arguments may only be merged when
||| the callee is known to have no side effects.  A function is pure if it
||| does not apply unknown closures, call foreign functions or impure
||| primitives, and only calls pure functions (greatest fixpoint).
module Lean.CSE

import Core.Name
import Lean.IR
import Lean.Opt
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

callees : Body -> List Name
callees (BLet _ _ (EFap f _) b) = f :: callees b
callees (BLet _ _ _ b) = callees b
callees (BJp _ _ jb r) = callees jb ++ callees r
callees (BCase _ _ alts) = concatMap (callees . altBody) alts
callees _ = []

||| local impurity: closure application or impure primitives
locallyImpure : Body -> Bool
locallyImpure (BLet _ _ (EAp _ _) _) = True
locallyImpure (BLet _ _ (EPrim sig _) b) = not sig.pure_ || locallyImpure b
locallyImpure (BLet _ _ _ b) = locallyImpure b
locallyImpure (BJp _ _ jb r) = locallyImpure jb || locallyImpure r
locallyImpure (BCase _ _ alts) = any (locallyImpure . altBody) alts
locallyImpure _ = False

export
pureFunctions : List Decl -> SortedSet Name
pureFunctions ds =
  let info = map (\d => (d.name, isNormal d && not (locallyImpure d.body), callees d.body)) ds
      start = fromList (map fst3 (filter snd3 info))
  in loop info start
  where
    fst3 : (Name, Bool, List Name) -> Name
    fst3 (n, _, _) = n

    snd3 : (Name, Bool, List Name) -> Bool
    snd3 (_, b, _) = b

    isNormal : Decl -> Bool
    isNormal d = case d.kind of
                   Normal => True
                   _ => False

    loop : List (Name, Bool, List Name) -> SortedSet Name -> SortedSet Name
    loop info s =
      let s' = fromList (map fst3 (filter (\(n, _, cs) => contains n s && all (\c => contains c s) cs) info)) in
      if length (Prelude.toList s') == length (Prelude.toList s) then s else loop info s'

||| A key identifying a pure expression
key : SortedSet Name -> Expr -> Maybe String
key pures e =
  case e of
    EFap f _ => if contains f pures then Just (show e) else Nothing
    EPrim sig _ => if sig.pure_ then Just (show e) else Nothing
    ECtor _ _ => Just (show e)
    EProj _ _ => Just (show e)
    ESProj _ _ _ => Just (show e)
    EBox _ _ => Just (show e)
    EUnbox _ _ => Just (show e)
    ECast _ _ => Just (show e)
    ELit _ => Just (show e)
    EPap _ _ => Just (show e)
    _ => Nothing

substA : SortedMap Var Var -> Arg -> Arg
substA m (AVar v) = AVar (fromMaybe v (lookup v m))
substA m AIrr = AIrr

substE : SortedMap Var Var -> Expr -> Expr
substE m e =
  let s : Var -> Var
      s v = fromMaybe v (lookup v m)
      sa : List Arg -> List Arg
      sa = map (substA m) in
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

cse : SortedSet Name -> SortedMap String (Var, Ty) -> SortedMap Var Var -> Body -> Body
cse pures avail ren (BLet x t e b) =
  let e' = substE ren e in
  case key pures e' of
    Just k => case lookup k avail of
                Just (y, ty) => if ty == t then cse pures avail (insert x y ren) b
                                else BLet x t e' (cse pures avail ren b)
                Nothing => BLet x t e' (cse pures (insert k (x, t) avail) ren b)
    Nothing => BLet x t e' (cse pures avail ren b)
cse pures avail ren (BJp j ps jb r) = BJp j ps (cse pures avail ren jb) (cse pures avail ren r)
cse pures avail ren (BCase x t alts) =
  BCase (fromMaybe x (lookup x ren)) t (map (\a => setAltBody a (cse pures avail ren (altBody a))) alts)
cse pures avail ren (BRet a) = BRet (substA ren a)
cse pures avail ren (BJmp j as) = BJmp j (map (substA ren) as)
cse pures avail ren b = b

export
cseDecl : SortedSet Name -> Decl -> Decl
cseDecl pures d = case d.kind of
  Normal => { body := cse pures empty empty d.body } d
  _ => d
