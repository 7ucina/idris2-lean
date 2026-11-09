||| Constructor field types, recovered from the typechecked context, used to
||| store primitive (and enumeration) fields unboxed in constructor objects.
module Lean.Layout

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.CompileExpr
import Libraries.Data.NatSet
import Lean.IR
import Lean.Prims
import Data.List
import Data.Maybe
import Data.SortedMap

%default covering

enumTy : Defs -> Name -> Core (Maybe Ty)
enumTy defs tn =
  do Just tdef <- lookupCtxtExact tn (gamma defs)
       | Nothing => pure Nothing
     case definition tdef of
       TCon _ _ _ _ _ (Just (c :: _)) _ =>
         do Just cdef <- lookupCtxtExact c (gamma defs)
              | Nothing => pure Nothing
            pure (findEnum (flags cdef))
       _ => pure Nothing
  where
    findEnum : List DefFlag -> Maybe Ty
    findEnum [] = Nothing
    findEnum (ConType (ENUM k) :: _) =
      Just (if k <= 0xff then TU8 else if k <= 0xffff then TU16 else TU32)
    findEnum (_ :: fs) = findEnum fs

fieldTy : Defs -> Term vars -> Core Ty
fieldTy defs (PrimVal _ (PrT t)) =
  pure (let ty = primTy t in if isScalar ty then ty else TObj)
fieldTy defs tm =
  case getFn tm of
    Ref _ (TyCon _) n => fromMaybe TObj <$> enumTy defs n
    _ => pure TObj

walk : Defs -> NatSet -> Nat -> Term vars -> Core (List Ty)
walk defs erased i (Bind _ _ (Pi _ _ _ argTy) sc) =
  if elem i erased then walk defs erased (S i) sc
  else do t <- fieldTy defs argTy
          ts <- walk defs erased (S i) sc
          pure (t :: ts)
walk defs erased i _ = pure []

||| Field types of a constructor (one per runtime field)
export
ctorFieldTys : {auto c : Ref Ctxt Defs} -> Name -> Core (Maybe (List Ty))
ctorFieldTys n =
  do defs <- get Ctxt
     Just gdef <- lookupCtxtExact n (gamma defs)
       | Nothing => pure Nothing
     ty <- normalise defs Env.empty (type gdef)
     Just <$> walk defs (eraseArgs gdef) 0 ty

||| Lean layout: boxed fields first (in order), then scalar fields sorted by
||| decreasing size.  Returns (numObjs, scalarBytes, field locations).
public export
Loc : Type
Loc = Either Nat (Nat, Ty)

placeScalars : Nat -> Nat -> List (Nat, Ty) -> (Nat, List (Nat, Loc))
placeScalars base off [] = (off, [])
placeScalars base off ((i, t) :: rest) =
  let (sz, locs) = placeScalars base (off + tySize t) rest
  in (sz, (i, Right (base + off, t)) :: locs)

export
layout : List Ty -> (Nat, Nat, List Loc)
layout tys =
  let indexed : List (Nat, Ty) = zip [0 .. length tys] tys
      boxed = map fst (filter (not . isScalar . snd) indexed)
      scalars = sortBy (\a, b => compare (tySize (snd b)) (tySize (snd a))) (filter (isScalar . snd) indexed)
      nobj = length boxed
      boxedLoc : List (Nat, Loc) = zip boxed (map Left [0 .. length boxed])
      (sz, scalarLoc) = placeScalars (nobj * 8) 0 scalars
      locs = map (\i => fromMaybe (Left 0) (lookup i (boxedLoc ++ scalarLoc))) (map fst indexed)
  in (nobj, sz, locs)

walkFn : Defs -> NatSet -> Nat -> Nat -> Term vars -> Core (Maybe (List Ty, Ty))
walkFn defs erased i Z tm =
  case tm of
    Bind _ _ (Pi _ _ _ _) _ => pure (Just ([], TObj))   -- returns a function
    _ => do t <- fieldTy defs tm
            pure (Just ([], t))
walkFn defs erased i (S k) (Bind _ _ (Pi _ _ _ argTy) sc) =
  if elem i erased then walkFn defs erased (S i) (S k) sc
  else do t <- fieldTy defs argTy
          Just (ts, r) <- walkFn defs erased (S i) k sc
            | Nothing => pure Nothing
          pure (Just (t :: ts, r))
walkFn defs erased i (S k) _ = pure Nothing

||| Declared representation of a function's parameters and result, from its
||| type (given the number of runtime parameters of the compiled definition).
export
fnSig : {auto c : Ref Ctxt Defs} -> Name -> Nat -> Core (Maybe (List Ty, Ty))
fnSig n arity =
  do defs <- get Ctxt
     Just gdef <- lookupCtxtExact n (gamma defs)
       | Nothing => pure Nothing
     ty <- normalise defs Env.empty (type gdef)
     walkFn defs (eraseArgs gdef) 0 arity ty
