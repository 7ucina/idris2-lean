||| Tail recursion modulo an associative accumulator.
|||
|||   f xs = ... ret (a + f ys + b)  ...  ret v
||| becomes
|||   f xs = f_acc xs 0
|||   f_acc xs acc = ... f_acc ys (acc + a + b) ... ret (acc + v)
||| for wrapping integer addition/multiplication (associative and
||| commutative), so the last recursive call becomes a loop.  This is the
||| transformation GCC performs on e.g. `nfib`/tree sizes; doing it in our IR
||| gives the same benefit with any C compiler.
module Lean.Accum

import Core.Name
import Lean.IR
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String

%default covering

-- An associative, commutative operation with an identity
record Op where
  constructor MkOp
  sig : PrimSig
  ident : Integer

isIntTy : Ty -> Bool
isIntTy t = isScalar t && t /= TF64

opOf : Ty -> PrimSig -> Maybe Op
opOf t sig =
  if not (isIntTy t) || sig.ret /= t then Nothing
  else if sig.cfun == "idr_add_" ++ tySuffix t then Just (MkOp sig 0)
  else if sig.cfun == "idr_mul_" ++ tySuffix t then Just (MkOp sig 1)
  else Nothing

-- Instructions of the current straight-line block, nearest first
Block : Type
Block = List (Var, Ty, Expr)

lookupDef : Var -> Block -> Maybe Expr
lookupDef v [] = Nothing
lookupDef v ((x, _, e) :: bs) = if x == v then Just e else lookupDef v bs

||| Leaves of the op-chain computing v (v defined in the block by op)
leaves : String -> Block -> Arg -> List Arg
leaves cf blk (AVar v) =
  case lookupDef v blk of
    Just (EPrim s [a, b]) => if s.cfun == cf then leaves cf blk a ++ leaves cf blk b else [AVar v]
    _ => [AVar v]
leaves cf blk a = [a]

||| variables defined by the chain (internal nodes)
internal : String -> Block -> Arg -> List Var
internal cf blk (AVar v) =
  case lookupDef v blk of
    Just (EPrim s [a, b]) => if s.cfun == cf then v :: internal cf blk a ++ internal cf blk b else []
    _ => []
internal cf blk _ = []

record Ctx where
  constructor MkCtx
  self : Name
  acc : Name
  ty : Ty

-- Classification of a return
data RetKind = Accumulating Op Var (List Arg)   -- op, the self-call var, other leaves
             | TailSelf
             | Plain

classify : Ctx -> Block -> Var -> RetKind
classify ctx blk z =
  case lookupDef z blk of
    Just (EFap g _) => if g == ctx.self then TailSelf else Plain
    Just (EPrim s [_, _]) =>
      case opOf ctx.ty s of
        Nothing => Plain
        Just op =>
          let ls = leaves s.cfun blk (AVar z)
              ints = internal s.cfun blk (AVar z)
              selfCalls = filter (\a => case a of
                                          AVar v => case lookupDef v blk of
                                                      Just (EFap g _) => g == ctx.self
                                                      _ => False
                                          _ => False) ls
          in case selfCalls of
               [] => Plain
               _ =>
                 -- the most recently defined self call
                 let pos : Arg -> Nat
                     pos = \a => case a of
                                   AVar v => fromMaybe 1000000 (findIndex (\(x, _, _) => x == v) blk)
                                   _ => 1000000
                     r = foldl (\best, a => if pos a < pos best then a else best) (AVar (-1)) selfCalls
                 in case r of
                      AVar rv =>
                        -- everything defined after r must be chain nodes or literals
                        let after = take (pos r) blk
                            ok = all (\(x, _, e) => (x `elem` ints) || isLit e) after
                            others = filter (/= r) ls
                        in if ok && length (filter (== r) ls) == 1 then Accumulating op rv others else Plain
                      _ => Plain
    _ => Plain
  where
    isLit : Expr -> Bool
    isLit (ELit _) = True
    isLit _ = False
    findIndex : (a -> Bool) -> List a -> Maybe Nat
    findIndex p xs = go 0 xs
      where go : Nat -> List a -> Maybe Nat
            go _ [] = Nothing
            go n (y :: ys) = if p y then Just n else go (S n) ys

-- Does the function have at least one accumulating return, all with one op?
scan : Ctx -> Block -> Body -> List (Maybe Op)
scan ctx blk (BLet x t e b) = scan ctx ((x, t, e) :: blk) b
scan ctx blk (BJp _ _ jb r) = scan ctx [] jb ++ scan ctx blk r
scan ctx blk (BCase _ _ alts) = concatMap (scan ctx blk . altBody) alts
scan ctx blk (BRet (AVar z)) = case classify ctx blk z of
                                 Accumulating op _ _ => [Just op]
                                 _ => [Nothing]
scan ctx blk _ = []

M : Type -> Type
M = State Int

fresh : M Var
fresh = do n <- get
           put (n + 1)
           pure n

||| fold `acc op leaf` over leaves, returning the final var
accumLets : Op -> Ty -> Var -> List Arg -> M (List (Var, Ty, Expr), Var)
accumLets op t acc [] = pure ([], acc)
accumLets op t acc (l :: ls) =
  do v <- fresh
     (rest, final) <- accumLets op t v ls
     pure ((v, t, EPrim op.sig [AVar acc, l]) :: rest, final)

||| Rebuild a block (reversed list) in front of a body
reblock : Block -> Body -> Body
reblock blk b = foldl (\acc, (x, t, e) => BLet x t e acc) b blk

transform : Ctx -> Op -> Var -> Block -> Body -> M Body
transform ctx op acc blk (BLet x t e b) = transform ctx op acc ((x, t, e) :: blk) b
transform ctx op acc blk (BJp j ps jb r) =
  do jb' <- transform ctx op acc [] jb
     r' <- transform ctx op acc [] r
     pure (reblock blk (BJp j ps jb' r'))
transform ctx op acc blk (BCase x t alts) =
  do alts' <- traverse (\a => setAltBody a <$> transform ctx op acc [] (altBody a)) alts
     pure (reblock blk (BCase x t alts'))
transform ctx op acc blk (BRet (AVar z)) =
  case classify ctx blk z of
    Accumulating _ rv others =>
      do let (before, call) = splitAt rv blk
         case call of
           Just args =>
             do (lets, acc') <- accumLets op ctx.ty acc others
                res <- fresh
                pure (reblock before (foldr (\(v, t, e), b => BLet v t e b)
                                        (BLet res ctx.ty (EFap ctx.acc (args ++ [AVar acc'])) (BRet (AVar res)))
                                        lets))
           Nothing => plain
    TailSelf =>
      case lookupDef z blk of
        Just (EFap _ args) =>
          let blk' = drop 1 blk in   -- z is the last instruction
          case blk of
            ((x, _, _) :: _) =>
              if x == z then do res <- fresh
                                pure (reblock blk' (BLet res ctx.ty (EFap ctx.acc (args ++ [AVar acc])) (BRet (AVar res))))
              else plain
            [] => plain
        _ => plain
    Plain => plain
  where
    plain : M Body
    plain = do v <- fresh
               pure (reblock blk (BLet v ctx.ty (EPrim op.sig [AVar acc, AVar z]) (BRet (AVar v))))

    -- instructions before the self call (dropping the call and the chain after it)
    splitAt : Var -> Block -> (Block, Maybe (List Arg))
    splitAt rv [] = ([], Nothing)
    splitAt rv ((x, t, e) :: bs) =
      if x == rv then case e of
                        EFap _ args => (bs, Just args)
                        _ => (bs, Nothing)
      else let (b', c) = splitAt rv bs in
           -- keep literal lets after the call (they may be leaves)
           (case e of
              ELit _ => (x, t, e) :: b'
              _ => b', c)
transform ctx op acc blk b = pure (reblock blk b)

maxVarB : Body -> Int
maxVarB (BLet x _ _ b) = max x (maxVarB b)
maxVarB (BJp _ ps jb r) = foldl max (max (maxVarB jb) (maxVarB r)) (map pvar ps)
maxVarB (BCase x _ alts) = foldl max x (map (maxVarB . altBody) alts)
maxVarB (BRet (AVar x)) = x
maxVarB _ = 0

||| Returns the transformed declaration(s): the wrapper and the worker
accumDecl : Decl -> List Decl
accumDecl d =
  case d.kind of
    Normal =>
      if not (isIntTy d.ret) then [d] else
      let accName = MN ("acc:" ++ show d.name) 0
          ctx = MkCtx d.name accName d.ret
          kinds = scan ctx [] d.body
          ops = catMaybes kinds
      in case ops of
           (op :: rest) =>
             if all (\o => o.sig.cfun == op.sig.cfun) rest
                then let start = foldl max (maxVarB d.body) (map pvar d.params) + 1
                         accV = start
                         body' = evalState (start + 1) (transform ctx op accV [] d.body)
                         worker = MkDecl accName (d.params ++ [MkParam accV d.ret False]) d.ret body' Normal
                         i0 = start + 1
                         wbody = BLet i0 d.ret (ELit (LInt op.ident d.ret))
                                   (BLet (i0 + 1) d.ret (EFap accName (map (AVar . pvar) d.params ++ [AVar i0]))
                                      (BRet (AVar (i0 + 1))))
                     in [{ body := wbody } d, worker]
                else [d]
           [] => [d]
    _ => [d]

export
accumulate : List Decl -> List Decl
accumulate = concatMap accumDecl
