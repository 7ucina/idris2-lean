||| A first-order IR with explicit memory management, modelled after Lean 4's
||| impure λRC IR ("Counting Immutable Beans", Ullrich & de Moura 2019).
module Lean.IR

import Core.Name
import Core.CompileExpr
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String

%default covering

------------------------------------------------------------------------
-- Types

public export
data Ty = TObj   -- lean_object* (possibly a tagged scalar)
        | TI8 | TI16 | TI32 | TI64
        | TU8 | TU16 | TU32 | TU64
        | TF64
        | TIrr   -- erased: represented as lean_box(0), never reference counted

export
Eq Ty where
  TObj == TObj = True
  TI8 == TI8 = True
  TI16 == TI16 = True
  TI32 == TI32 = True
  TI64 == TI64 = True
  TU8 == TU8 = True
  TU16 == TU16 = True
  TU32 == TU32 = True
  TU64 == TU64 = True
  TF64 == TF64 = True
  TIrr == TIrr = True
  _ == _ = False

export
Show Ty where
  show TObj = "obj"
  show TI8 = "i8"
  show TI16 = "i16"
  show TI32 = "i32"
  show TI64 = "i64"
  show TU8 = "u8"
  show TU16 = "u16"
  show TU32 = "u32"
  show TU64 = "u64"
  show TF64 = "f64"
  show TIrr = "irr"

||| Does a value of this type need reference counting?
export
isObj : Ty -> Bool
isObj TObj = True
isObj _ = False

export
isScalar : Ty -> Bool
isScalar TObj = False
isScalar TIrr = False
isScalar _ = True

||| Suffix used by the runtime's typed helpers (idr_box_i64, ...)
export
tySuffix : Ty -> String
tySuffix = show

export
cType : Ty -> String
cType TObj = "lean_object*"
cType TI8 = "int8_t"
cType TI16 = "int16_t"
cType TI32 = "int32_t"
cType TI64 = "int64_t"
cType TU8 = "uint8_t"
cType TU16 = "uint16_t"
cType TU32 = "uint32_t"
cType TU64 = "uint64_t"
cType TF64 = "double"
cType TIrr = "lean_object*"

||| Byte size of a scalar (for unboxed constructor fields)
export
tySize : Ty -> Nat
tySize TI8 = 1
tySize TU8 = 1
tySize TI16 = 2
tySize TU16 = 2
tySize TI32 = 4
tySize TU32 = 4
tySize _ = 8

------------------------------------------------------------------------
-- Syntax

public export
Var : Type
Var = Int

public export
data Arg = AVar Var | AIrr

export
Eq Arg where
  AVar x == AVar y = x == y
  AIrr == AIrr = True
  _ == _ = False

export
Show Arg where
  show (AVar v) = "x" ++ show v
  show AIrr = "◾"

||| Layout of a constructor: `size` boxed fields followed by scalar fields.
||| `fields` gives, for each source-level field, where it lives:
|||   Left i        -- boxed field number i
|||   Right (o, t)  -- scalar field at byte offset o (after the boxed fields) of type t
public export
record CtorInfo where
  constructor MkCtorInfo
  cname : Name
  tag : Int
  size : Nat        -- number of boxed fields
  ssize : Nat       -- bytes of scalar fields
  fields : List (Either Nat (Nat, Ty))

||| Nullary constructors with no scalar data are represented as lean_box(tag)
export
isScalarCtor : CtorInfo -> Bool
isScalarCtor c = c.size == 0 && c.ssize == 0

public export
data Lit = LInt Integer Ty     -- scalar literal of the given type
         | LDouble Double
         | LStr String
         | LInteger Integer    -- an Idris Integer (Lean Int object)
         | LTag Int            -- an object that is lean_box(n) (e.g. primitive types as values)

export
Show Lit where
  show (LInt i t) = show i ++ ":" ++ show t
  show (LDouble d) = show d
  show (LStr s) = show s
  show (LInteger i) = show i ++ "N"
  show (LTag i) = "#" ++ show i

||| A call to a C helper with a fixed signature
public export
record PrimSig where
  constructor MkPrimSig
  cfun : String
  params : List (Ty, Bool)   -- (type, borrowed?)
  ret : Ty
  pure_ : Bool               -- no side effects (may be removed if unused)

public export
data Expr : Type where
  ECtor  : CtorInfo -> List Arg -> Expr
  EReset : Nat -> Var -> Expr                      -- number of boxed fields, var
  EReuse : Var -> CtorInfo -> (updtHeader : Bool) -> List Arg -> Expr
  EProj  : Nat -> Var -> Expr                      -- boxed field i
  ESProj : Nat -> Ty -> Var -> Expr                -- scalar field at byte offset (from start of scalar area)
  EFap   : Name -> List Arg -> Expr                -- saturated call of a known function
  EPap   : Name -> List Arg -> Expr                -- partial application (closure)
  EAp    : Var -> List Arg -> Expr                 -- apply closure
  EBox   : Ty -> Var -> Expr                       -- box scalar of type ty
  EUnbox : Ty -> Var -> Expr                       -- unbox to scalar of type ty
  ELit   : Lit -> Expr
  EPrim  : PrimSig -> List Arg -> Expr
  ECast  : Ty -> Var -> Expr                       -- C cast between scalar types
  EIsShared : Var -> Expr
  ECopy  : Var -> Expr                            -- representation-changing copy (believe_me)

public export
record Param where
  constructor MkParam
  pvar : Var
  pty : Ty
  borrow : Bool

mutual
  public export
  data Body : Type where
    BLet   : Var -> Ty -> Expr -> Body -> Body
    BJp    : (jp : Int) -> List Param -> (jpBody : Body) -> (rest : Body) -> Body
    BCase  : Var -> Ty -> List Alt -> Body
    BRet   : Arg -> Body
    BJmp   : Int -> List Arg -> Body
    BUnreach : String -> Body
    -- memory management (introduced by later passes)
    BInc   : Var -> Nat -> Body -> Body
    BDec   : Var -> Body -> Body
    BDel   : Var -> Body -> Body                     -- free cell without touching fields
    BSetTag : Var -> Int -> Body -> Body
    BSet   : Var -> Nat -> Arg -> Body -> Body       -- set boxed field
    BSSet  : Var -> Nat -> Nat -> Ty -> Var -> Body -> Body  -- set scalar field: x, numObjs, offset, ty, value
    BRelease : Var -> Nat -> Body -> Body           -- lean_ctor_release(x, i)

  public export
  data Alt : Type where
    ACtor : CtorInfo -> Body -> Alt
    ALit  : Lit -> Body -> Alt
    ADefault : Body -> Alt

export
altBody : Alt -> Body
altBody (ACtor _ b) = b
altBody (ALit _ b) = b
altBody (ADefault b) = b

export
setAltBody : Alt -> Body -> Alt
setAltBody (ACtor c _) b = ACtor c b
setAltBody (ALit l _) b = ALit l b
setAltBody (ADefault _) b = ADefault b

public export
data DeclKind = Normal
              | Foreign (List String) (List CFType) CFType  -- C FFI function

public export
record Decl where
  constructor MkDecl
  name : Name
  params : List Param
  ret : Ty
  body : Body
  kind : DeclKind

------------------------------------------------------------------------
-- Free variables

export
argVars : List Arg -> List Var
argVars [] = []
argVars (AVar v :: as) = v :: argVars as
argVars (AIrr :: as) = argVars as

export
exprVars : Expr -> List Var
exprVars (ECtor _ as) = argVars as
exprVars (EReset _ x) = [x]
exprVars (EReuse x _ _ as) = x :: argVars as
exprVars (EProj _ x) = [x]
exprVars (ESProj _ _ x) = [x]
exprVars (EFap _ as) = argVars as
exprVars (EPap _ as) = argVars as
exprVars (EAp f as) = f :: argVars as
exprVars (EBox _ x) = [x]
exprVars (EUnbox _ x) = [x]
exprVars (ELit _) = []
exprVars (EPrim _ as) = argVars as
exprVars (ECast _ x) = [x]
exprVars (EIsShared x) = [x]
exprVars (ECopy x) = [x]

||| Free variables of a body.  Join points are handled via a map from join
||| point ids to their free variables.
export
freeVars : SortedMap Int (SortedSet Var) -> Body -> SortedSet Var
freeVars jps (BLet x _ e b) = delete x (freeVars jps b) `union` fromList (exprVars e)
freeVars jps (BJp j ps jb rest) =
  let jfv = foldl (\s, p => delete p.pvar s) (freeVars jps jb) ps
  in freeVars (insert j jfv jps) rest
freeVars jps (BCase x _ alts) = insert x (foldl (\s, a => union s (freeVars jps (altBody a))) empty alts)
freeVars jps (BRet (AVar x)) = singleton x
freeVars jps (BRet AIrr) = empty
freeVars jps (BJmp j as) = union (fromList (argVars as)) (fromMaybe empty (lookup j jps))
freeVars jps (BUnreach _) = empty
freeVars jps (BInc x _ b) = insert x (freeVars jps b)
freeVars jps (BDec x b) = insert x (freeVars jps b)
freeVars jps (BDel x b) = insert x (freeVars jps b)
freeVars jps (BSetTag x _ b) = insert x (freeVars jps b)
freeVars jps (BSet x _ a b) = insert x (union (fromList (argVars [a])) (freeVars jps b))
freeVars jps (BSSet x _ _ _ y b) = insert x (insert y (freeVars jps b))
freeVars jps (BRelease x _ b) = insert x (freeVars jps b)

------------------------------------------------------------------------
-- Pretty printing (for --dump debugging)

export
Show Expr where
  show (ECtor c as) = "ctor_" ++ show c.tag ++ "[" ++ show c.cname ++ "] " ++ unwords (map show as)
  show (EReset n x) = "reset[" ++ show n ++ "] x" ++ show x
  show (EReuse x c u as) = "reuse" ++ (if u then "!" else "") ++ " x" ++ show x ++ " in ctor_" ++ show c.tag ++ "[" ++ show c.cname ++ "] " ++ unwords (map show as)
  show (EProj i x) = "proj[" ++ show i ++ "] x" ++ show x
  show (ESProj o t x) = "sproj[" ++ show o ++ "," ++ show t ++ "] x" ++ show x
  show (EFap f as) = show f ++ " " ++ unwords (map show as)
  show (EPap f as) = "pap " ++ show f ++ " " ++ unwords (map show as)
  show (EAp f as) = "app x" ++ show f ++ " " ++ unwords (map show as)
  show (EBox t x) = "box[" ++ show t ++ "] x" ++ show x
  show (EUnbox t x) = "unbox[" ++ show t ++ "] x" ++ show x
  show (ELit l) = show l
  show (EPrim p as) = p.cfun ++ " " ++ unwords (map show as)
  show (ECast t x) = "cast[" ++ show t ++ "] x" ++ show x
  show (EIsShared x) = "isShared x" ++ show x
  show (ECopy x) = "copy x" ++ show x

indent : Nat -> String
indent n = pack (replicate (n * 2) ' ')

export
showBody : Nat -> Body -> String
showBody n (BLet x t e b) = indent n ++ "let x" ++ show x ++ " : " ++ show t ++ " = " ++ show e ++ ";\n" ++ showBody n b
showBody n (BJp j ps jb rest) =
  indent n ++ "block_" ++ show j ++ " (" ++ concat (intersperse ", " (map (\p => (if p.borrow then "@& " else "") ++ "x" ++ show p.pvar ++ " : " ++ show p.pty) ps)) ++ ") :=\n"
    ++ showBody (S n) jb ++ showBody n rest
showBody n (BCase x t alts) = indent n ++ "case x" ++ show x ++ " : " ++ show t ++ " of\n" ++ concatMap (showAlt (S n)) alts
  where
    showAlt : Nat -> Alt -> String
    showAlt n (ACtor c b) = indent n ++ show c.cname ++ " =>\n" ++ showBody (S n) b
    showAlt n (ALit l b) = indent n ++ show l ++ " =>\n" ++ showBody (S n) b
    showAlt n (ADefault b) = indent n ++ "default =>\n" ++ showBody (S n) b
showBody n (BRet a) = indent n ++ "ret " ++ show a ++ "\n"
showBody n (BJmp j as) = indent n ++ "jmp block_" ++ show j ++ " " ++ unwords (map show as) ++ "\n"
showBody n (BUnreach s) = indent n ++ "⊥ " ++ show s ++ "\n"
showBody n (BInc x k b) = indent n ++ "inc" ++ (if k == 1 then "" else "[" ++ show k ++ "]") ++ " x" ++ show x ++ ";\n" ++ showBody n b
showBody n (BDec x b) = indent n ++ "dec x" ++ show x ++ ";\n" ++ showBody n b
showBody n (BDel x b) = indent n ++ "del x" ++ show x ++ ";\n" ++ showBody n b
showBody n (BSetTag x t b) = indent n ++ "setTag x" ++ show x ++ " := " ++ show t ++ ";\n" ++ showBody n b
showBody n (BSet x i a b) = indent n ++ "set x" ++ show x ++ "[" ++ show i ++ "] := " ++ show a ++ ";\n" ++ showBody n b
showBody n (BSSet x _ o t y b) = indent n ++ "sset x" ++ show x ++ "[" ++ show o ++ ", " ++ show t ++ "] := x" ++ show y ++ ";\n" ++ showBody n b
showBody n (BRelease x i b) = indent n ++ "release x" ++ show x ++ "[" ++ show i ++ "];\n" ++ showBody n b

export
showDecl : Decl -> String
showDecl d =
  "def " ++ show d.name ++ " (" ++ concat (intersperse ", " (map (\p => (if p.borrow then "@& " else "") ++ "x" ++ show p.pvar ++ " : " ++ show p.pty) d.params)) ++ ") : " ++ show d.ret ++ " :=\n" ++ showBody 1 d.body
