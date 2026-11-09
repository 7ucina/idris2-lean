||| Explicit reference counting (port of Lean 4's ExplicitRC pass, which
||| implements the algorithm of "Counting Immutable Beans").
|||
||| Every variable of object type is either owned (must be consumed exactly
||| once) or borrowed.  We insert `inc` before uses that consume a value which
||| is still needed afterwards (or which is borrowed), and `dec` as soon as an
||| owned value is dead.
module Lean.RC

import Core.Name
import Lean.IR
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

%default covering

record VarInfo where
  constructor MkVI
  ref : Bool       -- may be a heap object
  consume : Bool   -- owned

public export
record RCCtx where
  constructor MkRCCtx
  vars : SortedMap Var VarInfo
  jpLive : SortedMap Int (SortedSet Var)
  jpParams : SortedMap Int (List Param)
  paramBorrow : Name -> Maybe (List Bool)

getVI : RCCtx -> Var -> VarInfo
getVI ctx x = fromMaybe (MkVI False False) (lookup x ctx.vars)

mustConsume : RCCtx -> Var -> Bool
mustConsume ctx x = let i = getVI ctx x in i.ref && i.consume

addInc : Var -> Nat -> Body -> Body
addInc x Z b = b
addInc x n b = BInc x n b

addDecIfNeeded : RCCtx -> Var -> Body -> SortedSet Var -> Body
addDecIfNeeded ctx x b live =
  if mustConsume ctx x && not (contains x live) then BDec x b else b

indexed : List a -> List (Nat, a)
indexed xs = zip [0 .. length xs] xs

isFirstOcc : List Arg -> Nat -> Var -> Bool
isFirstOcc xs i x = all (\(j, a) => j >= i || a /= AVar x) (indexed xs)

isBorrowParamAux : Var -> List Arg -> (Nat -> Bool) -> Bool
isBorrowParamAux x xs consumeP = any (\(i, a) => a == AVar x && not (consumeP i)) (indexed xs)

numConsumptions : Var -> List Arg -> (Nat -> Bool) -> Nat
numConsumptions x xs consumeP = length (filter (\(i, a) => a == AVar x && consumeP i) (indexed xs))

addIncBeforeAux : RCCtx -> List Arg -> (Nat -> Bool) -> Body -> SortedSet Var -> Body
addIncBeforeAux ctx xs consumeP b liveAfter = foldl step b (indexed xs)
  where
    step : Body -> (Nat, Arg) -> Body
    step b (i, AIrr) = b
    step b (i, AVar x) =
      let info = getVI ctx x in
      if not info.ref || not (isFirstOcc xs i x) then b
      else let n = numConsumptions x xs consumeP
               incs = if not info.consume || contains x liveAfter || isBorrowParamAux x xs consumeP
                         then n else minus n 1
           in addInc x incs b

nth : Nat -> List Bool -> Bool
nth i bs = fromMaybe False (getAt i bs)
  where
    getAt : Nat -> List Bool -> Maybe Bool
    getAt _ [] = Nothing
    getAt Z (x :: _) = Just x
    getAt (S k) (_ :: xs) = getAt k xs

||| borrow flags -> "is parameter i consumed"
consumedBy : List Bool -> Nat -> Bool
consumedBy borrows i = not (nth i borrows)

addIncBefore : RCCtx -> List Arg -> List Bool -> Body -> SortedSet Var -> Body
addIncBefore ctx xs borrows = addIncBeforeAux ctx xs (consumedBy borrows)

addIncBeforeConsumeAll : RCCtx -> List Arg -> Body -> SortedSet Var -> Body
addIncBeforeConsumeAll ctx xs = addIncBeforeAux ctx xs (const True)

addDecAfterFullApp : RCCtx -> List Arg -> List Bool -> Body -> SortedSet Var -> Body
addDecAfterFullApp ctx xs borrows b live = foldl step b (indexed xs)
  where
    step : Body -> (Nat, Arg) -> Body
    step b (i, AIrr) = b
    step b (i, AVar x) =
      if mustConsume ctx x && isFirstOcc xs i x
           && isBorrowParamAux x xs (consumedBy borrows) && not (contains x live)
         then BDec x b else b

addDecForDeadParams : RCCtx -> List Param -> Body -> SortedSet Var -> Body
addDecForDeadParams ctx ps b live =
  foldl (\b, p => if not p.borrow && isObj p.pty && not (contains p.pvar live) then BDec p.pvar b else b) b ps

withParams : RCCtx -> List Param -> RCCtx
withParams ctx ps = { vars $= \m => foldl (\m, p => insert p.pvar (MkVI (isObj p.pty) (not p.borrow)) m) m ps } ctx

consumeExpr : RCCtx -> Expr -> Bool
consumeExpr ctx (EProj _ x) = (getVI ctx x).consume
consumeExpr ctx _ = True

exprArgs : Expr -> List Arg
exprArgs e = map AVar (exprVars e)

processLet : RCCtx -> Var -> Ty -> Expr -> Body -> SortedSet Var -> Body
processLet ctx z t e b live =
  case e of
    ECtor _ ys => addIncBeforeConsumeAll ctx ys (BLet z t e b) live
    EReuse _ _ _ ys => addIncBeforeConsumeAll ctx ys (BLet z t e b) live
    EPap _ ys => addIncBeforeConsumeAll ctx ys (BLet z t e b) live
    EAp f ys => addIncBeforeConsumeAll ctx (ys ++ [AVar f]) (BLet z t e b) live
    EProj _ x =>
      let b1 = addDecIfNeeded ctx x b live
          b2 = if (getVI ctx x).consume then addInc z 1 b1 else b1
      in BLet z t e b2
    ESProj _ _ x => BLet z t e (addDecIfNeeded ctx x b live)
    EUnbox _ x => BLet z t e (addDecIfNeeded ctx x b live)
    EIsShared x => BLet z t e (addDecIfNeeded ctx x b live)
    EFap f ys =>
      let borrows = fromMaybe [] (ctx.paramBorrow f)
          b1 = addDecAfterFullApp ctx ys borrows b live
      in addIncBefore ctx ys borrows (BLet z t e b1) live
    EPrim sig ys =>
      let borrows = map snd sig.params
          b1 = addDecAfterFullApp ctx ys borrows b live
      in addIncBefore ctx ys borrows (BLet z t e b1) live
    ECopy y => if isObj t
                  then addIncBeforeConsumeAll ctx [AVar y] (BLet z t e b) live
                  else BLet z t e (addDecIfNeeded ctx y b live)
    ECast _ y => BLet z t e b
    EBox _ _ => BLet z t e b
    ELit _ => BLet z t e b
    EReset _ _ => BLet z t e b

||| Values that are certainly tagged scalars (lean_box) need no RC
isBoxedScalar : Expr -> Bool
isBoxedScalar (ECtor c _) = isScalarCtor c
isBoxedScalar (ELit (LInteger i)) = i >= -2147483647 && i <= 2147483647
isBoxedScalar (ELit (LTag _)) = True
isBoxedScalar _ = False

mutual
  visit : RCCtx -> Body -> (Body, SortedSet Var)
  visit ctx (BLet z t e b) =
    let ctx' = { vars $= insert z (MkVI (isObj t && not (isBoxedScalar e)) (consumeExpr ctx e)) } ctx
        (b', bLive) = visit ctx' b
        b'' = addDecIfNeeded ctx' z b' bLive
        b3 = processLet ctx' z t e b'' bLive
        live = delete z (union bLive (fromList (exprVars e)))
    in (b3, live)
  visit ctx (BJp j ps jb rest) =
    let ctxJ = withParams ctx ps
        (jb', jbLive) = visit ctxJ jb
        jb'' = addDecForDeadParams ctxJ ps jb' jbLive
        jl = foldl (\s, p => delete p.pvar s) jbLive ps
        ctx2 = { jpLive $= insert j jl, jpParams $= insert j ps } ctx
        (rest', restLive) = visit ctx2 rest
    in (BJp j ps jb'' rest', restLive)
  visit ctx b@(BCase x ty alts) =
    let caseLive = freeVars ctx.jpLive b
        alts' = map (visitAlt caseLive) alts
    in (BCase x ty alts', caseLive)
    where
      visitAlt : SortedSet Var -> Alt -> Alt
      visitAlt caseLive alt =
        let ctxA = case alt of
                     ACtor c _ => if isScalarCtor c
                                     then { vars $= updateExisting (\i => { ref := False } i) x } ctx
                                     else ctx
                     _ => ctx
            (ab, altLive) = visit ctxA (altBody alt)
            ab' = foldl (\acc, v => if not (contains v altLive) && mustConsume ctxA v then BDec v acc else acc)
                        ab (Prelude.toList caseLive)
        in setAltBody alt ab'
  visit ctx b@(BRet (AVar x)) =
    let i = getVI ctx x in
    (if i.ref && not i.consume then BInc x 1 b else b, singleton x)
  visit ctx b@(BRet AIrr) = (b, empty)
  visit ctx b@(BJmp j ys) =
    let jl = fromMaybe empty (lookup j ctx.jpLive)
        ps = fromMaybe [] (lookup j ctx.jpParams)
        b' = addIncBefore ctx ys (map borrow ps) b jl
    in (b', union jl (fromList (argVars ys)))
  visit ctx b@(BUnreach _) = (b, empty)
  visit ctx b = (b, freeVars ctx.jpLive b)

export
explicitRC : (Name -> Maybe (List Bool)) -> Decl -> Decl
explicitRC borrowOf d =
  case d.kind of
    Foreign _ _ _ => d
    Normal =>
      let ctx = withParams (MkRCCtx empty empty empty borrowOf) d.params
          (b, live) = visit ctx d.body
      in { body := addDecForDeadParams ctx d.params b live } d
