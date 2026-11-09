||| Lowering from Idris2's ANF to the λRC-style IR.
|||
||| Types assigned here are *natural* types: primitive operations produce and
||| consume their natural scalar type, everything else is an object.  The
||| Lean.Types pass later decides the representation of every variable and
||| inserts box/unbox coercions.
module Lean.Lower

import Core.Name
import Core.TT
import Core.CompileExpr
import Compiler.ANF
import Lean.IR
import Lean.Prims
import Lean.Layout
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.Vect

%default covering

------------------------------------------------------------------------
-- Global information

public export
record GlobalInfo where
  constructor MkGlobalInfo
  ctors : SortedMap Name (Int, Nat)        -- tag, arity
  funs : SortedMap Name Nat                -- arity of every callable definition
  untagged : SortedMap Name Int            -- tags invented for constructors without one
  fieldTys : SortedMap Name (List Ty)       -- runtime field types of constructors

export
mkGlobalInfo : SortedMap Name (List Ty) -> List (Name, ANFDef) -> GlobalInfo
mkGlobalInfo ftys defs =
  let ctors = fromList (mapMaybe isCon defs)
      found = concatMap scanDef defs
      nonNullary = nub (map fst (filter snd found))
      nullary = filter (\n => not (n `elem` nonNullary)) (nub (mapMaybe isUntagged defs ++ map fst found))
      untagged = fromList (zip nullary (map (\i => 1000 + i) [0 .. cast (length nullary)])
                           ++ zip nonNullary (map (\i => i `mod` 244) [0 .. cast (length nonNullary)]))
      funs = fromList (mapMaybe arity defs)
  in MkGlobalInfo ctors funs untagged ftys
  where
    isCon : (Name, ANFDef) -> Maybe (Name, (Int, Nat))
    isCon (n, MkACon t a _) = Just (n, (fromMaybe 0 t, a))
    isCon _ = Nothing

    isUntagged : (Name, ANFDef) -> Maybe Name
    isUntagged (n, MkACon Nothing _ _) = Just n
    isUntagged _ = Nothing

    -- constructors without tags (type constructors used in type-case)
    scan : ANF -> List (Name, Bool)
    scan (ALet _ _ a b) = scan a ++ scan b
    scan (ACon _ n _ Nothing as) = [(n, not (isNil as))]
    scan (AConCase _ _ alts d) =
      concatMap (\(MkAConAlt n _ t as b) => (if isNothing t then [(n, not (isNil as))] else []) ++ scan b) alts
        ++ maybe [] scan d
    scan (AConstCase _ _ alts d) = concatMap (\(MkAConstAlt _ b) => scan b) alts ++ maybe [] scan d
    scan _ = []

    scanDef : (Name, ANFDef) -> List (Name, Bool)
    scanDef (_, MkAFun _ b) = scan b
    scanDef (_, MkAError b) = scan b
    scanDef _ = []

    arity : (Name, ANFDef) -> Maybe (Name, Nat)
    arity (n, MkAFun args _) = Just (n, length args)
    arity (n, MkAForeign _ args _) = Just (n, length args)
    arity (n, MkAError _) = Just (n, 0)
    arity _ = Nothing

export
ctorInfo : GlobalInfo -> Name -> Maybe Int -> Nat -> CtorInfo
ctorInfo g n mtag nargs =
  let tag = case mtag of
              Just t => t
              Nothing => fromMaybe 0 (lookup n g.untagged)
  in case lookup n g.fieldTys of
       Just tys => if length tys == nargs
                      then let (nobj, ssz, locs) = layout tys in MkCtorInfo n tag nobj ssz locs
                      else MkCtorInfo n tag nargs 0 (map Left (take nargs [0..]))
       Nothing => MkCtorInfo n tag nargs 0 (map Left (take nargs [0..]))

------------------------------------------------------------------------
-- Monad

record LState where
  constructor MkLState
  nextVar : Int
  nextJp : Int

L : Type -> Type
L = State LState

fresh : L Var
fresh = do s <- get
           put ({ nextVar $= (+1) } s)
           pure s.nextVar

freshJp : L Int
freshJp = do s <- get
             put ({ nextJp $= (+1) } s)
             pure s.nextJp

data Cont = KRet | KFn (Arg -> L Body)

kont : Cont -> Arg -> L Body
kont KRet a = pure (BRet a)
kont (KFn f) a = f a

record Env where
  constructor MkEnv
  global : GlobalInfo
  ren : SortedMap Int Arg
  -- constructor shapes known in the current scope: con name, field vars, the value
  shapes : List (Name, List Int, Var)

lv : Env -> AVar -> Arg
lv env (ALocal i) = fromMaybe (AVar i) (lookup i env.ren)
lv env ANull = AIrr

||| Bind the result of an expression to a fresh variable and continue
bindE : Ty -> Expr -> Cont -> L Body
bindE t e k = do x <- fresh
                 rest <- kont k (AVar x)
                 pure (BLet x t e rest)

||| If the continuation is not a return, create a join point for it so that
||| branching code can jump to it.
withJoin : Cont -> (Cont -> L Body) -> L Body
withJoin KRet f = f KRet
withJoin (KFn g) f =
  do j <- freshJp
     p <- fresh
     rest <- g (AVar p)
     body <- f (KFn (\a => pure (BJmp j [a])))
     pure (BJp j [MkParam p TObj False] rest body)

------------------------------------------------------------------------
-- Constants

export
constTy : Constant -> Ty
constTy (I _) = TI64
constTy (I8 _) = TI8
constTy (I16 _) = TI16
constTy (I32 _) = TI32
constTy (I64 _) = TI64
constTy (B8 _) = TU8
constTy (B16 _) = TU16
constTy (B32 _) = TU32
constTy (B64 _) = TU64
constTy (Ch _) = TU32
constTy (Db _) = TF64
constTy _ = TObj

export
constLit : Constant -> Maybe Lit
constLit (I i) = Just (LInt (cast i) TI64)
constLit (I8 i) = Just (LInt (cast i) TI8)
constLit (I16 i) = Just (LInt (cast i) TI16)
constLit (I32 i) = Just (LInt (cast i) TI32)
constLit (I64 i) = Just (LInt (cast i) TI64)
constLit (B8 i) = Just (LInt (cast i) TU8)
constLit (B16 i) = Just (LInt (cast i) TU16)
constLit (B32 i) = Just (LInt (cast i) TU32)
constLit (B64 i) = Just (LInt (cast i) TU64)
constLit (Ch c) = Just (LInt (cast (ord c)) TU32)
constLit (Db d) = Just (LDouble d)
constLit (Str s) = Just (LStr s)
constLit (BI i) = Just (LInteger i)
constLit (PrT t) = Just (LTag (2000 + primTag t))
  where
    primTag : PrimType -> Int
    primTag IntType = 0
    primTag Int8Type = 1
    primTag Int16Type = 2
    primTag Int32Type = 3
    primTag Int64Type = 4
    primTag IntegerType = 5
    primTag Bits8Type = 6
    primTag Bits16Type = 7
    primTag Bits32Type = 8
    primTag Bits64Type = 9
    primTag StringType = 10
    primTag CharType = 11
    primTag DoubleType = 12
    primTag WorldType = 13
constLit _ = Nothing

litTy : Lit -> Ty
litTy (LInt _ t) = t
litTy (LDouble _) = TF64
litTy _ = TObj

------------------------------------------------------------------------
-- Lowering

traverseOpt : (a -> L b) -> Maybe a -> L (Maybe b)
traverseOpt f Nothing = pure Nothing
traverseOpt f (Just x) = Just <$> f x

mutual
  lowerA : Env -> ANF -> Cont -> L Body
  lowerA env (AV _ v) k = kont k (lv env v)
  lowerA env (AAppName _ _ n args) k =
    case lookup n env.global.funs of
      Just _ => bindE TObj (EFap n (map (lv env) args)) k
      Nothing => pure (BUnreach ("call to undefined function " ++ show n))
  lowerA env (AUnderApp _ n missing args) k =
    bindE TObj (EPap n (map (lv env) args)) k
  lowerA env (AApp _ _ c a) k =
    case lv env c of
      AVar f => bindE TObj (EAp f [lv env a]) k
      AIrr => pure (BUnreach "application of erased value")
  lowerA env (ALet _ v rhs body) k =
    lowerA env rhs (KFn (\a => lowerA ({ ren $= insert v a } env) body k))
  lowerA env (ACon _ n ci tag args) k =
    case find (\(cn, fs, _) => cn == n && map ALocal fs == args) env.shapes of
      Just (_, _, x) => kont k (AVar x)   -- rebuilding the scrutinee: reuse it
      Nothing => bindE TObj (ECtor (ctorInfo env.global n tag (length args)) (map (lv env) args)) k
  lowerA env (AOp _ _ op args) k = lowerOp env op (map (lv env) (toList args)) k
  lowerA env (AExtPrim _ _ n args) k = lowerExt n (map (lv env) args) k
  lowerA env (AConCase _ sc alts def) k =
    withJoin k $ \k' =>
      do (x, pre) <- scrutVar (lv env sc)
         alts' <- traverse (lowerConAlt env x k') alts
         def' <- traverseOpt (\d => lowerA env d k') def
         pure (pre (BCase x TObj (alts' ++ maybe [] (\d => [ADefault d]) def')))
  lowerA env (AConstCase _ sc alts def) k =
    withJoin k $ \k' =>
      do (x, pre) <- scrutVar (lv env sc)
         alts' <- traverse (lowerConstAlt env k') alts
         def' <- traverseOpt (\d => lowerA env d k') def
         let ty = case alts of
                    (MkAConstAlt c _ :: _) => constTy c
                    [] => TObj
         pure (pre (BCase x ty (catMaybes alts' ++ maybe [] (\d => [ADefault d]) def')))
  lowerA env (APrimVal _ c) k =
    case constLit c of
      Just l => bindE (litTy l) (ELit l) k
      Nothing => kont k AIrr
  lowerA env (AErased _) k = kont k AIrr
  lowerA env (ACrash _ msg) k = pure (BUnreach msg)

  scrutVar : Arg -> L (Var, Body -> Body)
  scrutVar (AVar x) = pure (x, id)
  scrutVar AIrr = do x <- fresh
                     pure (x, BLet x TObj (ELit (LInt 0 TI64)))

  lowerConAlt : Env -> Var -> Cont -> AConAlt -> L Alt
  lowerConAlt env x k (MkAConAlt n ci tag args body) =
    do let info = ctorInfo env.global n tag (length args)
       let env' = { shapes $= ((n, args, x) ::) } env
       body' <- lowerA env' body k
       let projs = zip args info.fields
       pure (ACtor info (foldr proj body' projs))
    where
      proj : (Int, Either Nat (Nat, Ty)) -> Body -> Body
      proj (a, Left i) b = BLet a TObj (EProj i x) b
      proj (a, Right (off, t)) b = BLet a t (ESProj off t x) b

  lowerConstAlt : Env -> Cont -> AConstAlt -> L (Maybe Alt)
  lowerConstAlt env k (MkAConstAlt c body) =
    case constLit c of
      Just l => pure (Just (ALit l !(lowerA env body k)))
      Nothing => pure Nothing

  lowerOp : Env -> PrimFn ar -> List Arg -> Cont -> L Body
  lowerOp env BelieveMe [_, _, a] k =
    case a of
      AVar x => bindE TObj (ECopy x) k
      AIrr => kont k AIrr
  lowerOp env Crash [_, msg] k = bindE TObj (EPrim crashSig [msg]) (KFn (\_ => pure (BUnreach "")))
  lowerOp env op args k =
    case primSig op of
      Just sig => bindE sig.ret (EPrim sig args) k
      Nothing => pure (BUnreach ("unsupported primitive " ++ show op))

  lowerExt : Name -> List Arg -> Cont -> L Body
  lowerExt n args k =
    case extPrim n args of
      Just (Left l) => bindE (litTy l) (ELit l) k
      Just (Right (sig, args')) => bindE sig.ret (EPrim sig args') k
      Nothing => pure (BUnreach ("unsupported external primitive " ++ show n))


------------------------------------------------------------------------
-- Foreign functions

||| The Idris-side representation of a C FFI type
export
cfTy : CFType -> Ty
cfTy CFInt = TI64
cfTy CFInt8 = TI8
cfTy CFInt16 = TI16
cfTy CFInt32 = TI32
cfTy CFInt64 = TI64
cfTy CFUnsigned8 = TU8
cfTy CFUnsigned16 = TU16
cfTy CFUnsigned32 = TU32
cfTy CFUnsigned64 = TU64
cfTy CFDouble = TF64
cfTy CFChar = TU32
cfTy CFWorld = TIrr
cfTy (CFIORes t) = cfTy t
cfTy _ = TObj

maxVar : ANF -> Int
maxVar (AV _ (ALocal i)) = i
maxVar (ALet _ v a b) = max v (max (maxVar a) (maxVar b))
maxVar (AConCase _ _ alts d) =
  foldl max (maybe 0 maxVar d) (map (\(MkAConAlt _ _ _ as b) => foldl max (maxVar b) as) alts)
maxVar (AConstCase _ _ alts d) =
  foldl max (maybe 0 maxVar d) (map (\(MkAConstAlt _ b) => maxVar b) alts)
maxVar _ = 0

------------------------------------------------------------------------
-- Entry point

export
lowerDef : GlobalInfo -> (Name, ANFDef) -> Maybe Decl
lowerDef g (n, MkAFun args body) =
  let start = foldl max (maxVar body) args + 1
      env = MkEnv g empty []
      b = evalState (MkLState start 0) (lowerA env body KRet)
  in Just (MkDecl n (map (\a => MkParam a TObj False) args) TObj b Normal)
lowerDef g (n, MkAError body) =
  let env = MkEnv g empty []
      b = evalState (MkLState (maxVar body + 1) 0) (lowerA env body KRet)
  in Just (MkDecl n [] TObj b Normal)
lowerDef g (n, MkAForeign ccs fargs ret) =
  let ps = zipWith (\i, t => MkParam i (cfTy t) True) [0 .. cast (length fargs)] fargs
  in Just (MkDecl n ps (cfTy ret) (BUnreach "foreign") (Foreign ccs fargs ret))
lowerDef g _ = Nothing
