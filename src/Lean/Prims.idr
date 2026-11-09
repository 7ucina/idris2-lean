||| Primitive operations: their C implementation and calling convention.
module Lean.Prims

import Core.Name
import Core.TT
import Lean.IR
import Data.List
import Data.Maybe
import Data.String

%default covering

export
primTy : PrimType -> Ty
primTy IntType = TI64
primTy Int8Type = TI8
primTy Int16Type = TI16
primTy Int32Type = TI32
primTy Int64Type = TI64
primTy Bits8Type = TU8
primTy Bits16Type = TU16
primTy Bits32Type = TU32
primTy Bits64Type = TU64
primTy CharType = TU32
primTy DoubleType = TF64
primTy WorldType = TIrr
primTy IntegerType = TObj
primTy StringType = TObj

||| A pure operation on borrowed arguments
op : String -> List Ty -> Ty -> PrimSig
op f ts r = MkPrimSig f (map (\t => (t, True)) ts) r True

-- Classify primitive types
data Kind = KScalar Ty | KInteger | KString | KOther

kind : PrimType -> Kind
kind IntegerType = KInteger
kind StringType = KString
kind WorldType = KOther
kind t = KScalar (primTy t)

arith : String -> String -> PrimType -> Maybe PrimSig
arith name integerFn ty =
  case kind ty of
    KScalar t => Just (op ("idr_" ++ name ++ "_" ++ tySuffix t) [t, t] t)
    KInteger => Just (op integerFn [TObj, TObj] TObj)
    _ => Nothing

cmp : String -> PrimType -> Maybe PrimSig
cmp name ty =
  case kind ty of
    KScalar t => Just (op ("idr_" ++ name ++ "_" ++ tySuffix t) [t, t] TI64)
    KInteger => Just (op ("idr_integer_" ++ name) [TObj, TObj] TI64)
    KString => Just (op ("idr_str_" ++ name) [TObj, TObj] TI64)
    _ => Nothing

isSigned : Ty -> Bool
isSigned TI8 = True
isSigned TI16 = True
isSigned TI32 = True
isSigned TI64 = True
isSigned _ = False

isIntLike : Ty -> Bool
isIntLike TF64 = False
isIntLike t = isScalar t

||| C code to convert between primitive types.  The string is used as a
||| function name applied to the argument, so it may also be a cast prefix.
castFn : PrimType -> PrimType -> Maybe String
castFn from to =
  case (kind from, kind to) of
    (KScalar f, KScalar t) =>
      if f == t then Just ""
      else if f == TF64 then Just ("(" ++ cType t ++ ")(int64_t)")
      else Just ("(" ++ cType t ++ ")")
    (KScalar TF64, KInteger) => Just "idr_integer_of_double"
    (KScalar TU64, KInteger) => Just "idr_integer_of_u64"
    (KScalar f, KInteger) => Just "idr_integer_of_i64"
    (KInteger, KScalar TF64) => Just "idr_integer_to_double"
    (KInteger, KScalar t) => Just ("(" ++ cType t ++ ")idr_integer_to_i64")
    (KScalar TF64, KString) => Just "idr_str_of_double"
    (KScalar TU32, KString) =>
       case from of
         CharType => Just "idr_str_of_char"
         _ => Just "idr_str_of_i64"
    (KScalar TU64, KString) => Just "idr_str_of_u64"
    (KScalar _, KString) => Just "idr_str_of_i64"
    (KInteger, KString) => Just "idr_integer_to_string"
    (KString, KScalar TF64) => Just "idr_str_to_double"
    (KString, KScalar t) =>
       case to of
         CharType => Just "idr_str_to_char"
         _ => Just ("(" ++ cType t ++ ")idr_str_to_i64")
    (KString, KInteger) => Just "idr_str_to_integer"
    (KInteger, KInteger) => Just ""
    (KString, KString) => Just ""
    _ => Nothing

export
crashSig : PrimSig
crashSig = MkPrimSig "idr_crash_v" [(TObj, True)] TObj False

export
primSig : PrimFn ar -> Maybe PrimSig
primSig (Add ty) = arith "add" "lean_int_add" ty
primSig (Sub ty) = arith "sub" "lean_int_sub" ty
primSig (Mul ty) = arith "mul" "lean_int_mul" ty
primSig (Div ty) = arith "div" "idr_integer_div" ty
primSig (Mod ty) = arith "mod" "idr_integer_mod" ty
primSig (Neg ty) =
  case kind ty of
    KScalar t => Just (op ("idr_neg_" ++ tySuffix t) [t] t)
    KInteger => Just (op "lean_int_neg" [TObj] TObj)
    _ => Nothing
primSig (ShiftL ty) = arith "shl" "idr_integer_shl" ty
primSig (ShiftR ty) = arith "shr" "idr_integer_shr" ty
primSig (BAnd ty) = arith "and" "idr_integer_and" ty
primSig (BOr ty) = arith "or" "idr_integer_or" ty
primSig (BXOr ty) = arith "xor" "idr_integer_xor" ty
primSig (LT ty) = cmp "lt" ty
primSig (LTE ty) = cmp "le" ty
primSig (EQ ty) = cmp "eq" ty
primSig (GTE ty) = cmp "ge" ty
primSig (GT ty) = cmp "gt" ty
primSig StrLength = Just (op "idr_str_length" [TObj] TI64)
primSig StrHead = Just (op "idr_str_head" [TObj] TU32)
primSig StrTail = Just (op "idr_str_tail" [TObj] TObj)
primSig StrIndex = Just (op "idr_str_index" [TObj, TI64] TU32)
primSig StrCons = Just (op "idr_str_cons" [TU32, TObj] TObj)
primSig StrAppend = Just (MkPrimSig "idr_str_append" [(TObj, False), (TObj, True)] TObj True)
primSig StrReverse = Just (op "idr_str_reverse" [TObj] TObj)
primSig StrSubstr = Just (op "idr_str_substr" [TI64, TI64, TObj] TObj)
primSig DoubleExp = Just (op "exp" [TF64] TF64)
primSig DoubleLog = Just (op "log" [TF64] TF64)
primSig DoublePow = Just (op "pow" [TF64, TF64] TF64)
primSig DoubleSin = Just (op "sin" [TF64] TF64)
primSig DoubleCos = Just (op "cos" [TF64] TF64)
primSig DoubleTan = Just (op "tan" [TF64] TF64)
primSig DoubleASin = Just (op "asin" [TF64] TF64)
primSig DoubleACos = Just (op "acos" [TF64] TF64)
primSig DoubleATan = Just (op "atan" [TF64] TF64)
primSig DoubleSqrt = Just (op "sqrt" [TF64] TF64)
primSig DoubleFloor = Just (op "floor" [TF64] TF64)
primSig DoubleCeiling = Just (op "ceil" [TF64] TF64)
primSig (Cast from to) =
  do f <- castFn from to
     let tf = primTy from
     let tt = primTy to
     pure (op f [if isScalar tf then tf else TObj] (if isScalar tt then tt else TObj))
primSig BelieveMe = Nothing
primSig Crash = Nothing

baseName : Name -> String
baseName (NS _ n) = baseName n
baseName (UN (Basic s)) = s
baseName (DN _ n) = baseName n
baseName n = show n

lastN : Nat -> List a -> List a
lastN n xs = drop (minus (length xs) n) xs

||| External primitives (%extern).  Arguments include erased type arguments
||| and the world token, so we index from the end.
export
extPrim : Name -> List Arg -> Maybe (Either Lit (PrimSig, List Arg))
extPrim n args =
  case baseName n of
    "prim__newIORef" => Just (Right (MkPrimSig "idr_ioref_new" [(TObj, False)] TObj False, take 1 (lastN 2 args)))
    "prim__readIORef" => Just (Right (MkPrimSig "idr_ioref_read" [(TObj, True)] TObj False, take 1 (lastN 2 args)))
    "prim__writeIORef" => Just (Right (MkPrimSig "idr_ioref_write" [(TObj, True), (TObj, False)] TObj False, take 2 (lastN 3 args)))
    "prim__newArray" => Just (Right (MkPrimSig "idr_array_new" [(TI64, True), (TObj, False)] TObj False, take 2 (lastN 3 args)))
    "prim__arrayGet" => Just (Right (MkPrimSig "idr_array_get" [(TObj, True), (TI64, True)] TObj False, take 2 (lastN 3 args)))
    "prim__arraySet" => Just (Right (MkPrimSig "idr_array_set" [(TObj, True), (TI64, True), (TObj, False)] TObj False, take 3 (lastN 4 args)))
    "prim__onCollect" => Just (Right (MkPrimSig "idr_on_collect" [(TObj, False), (TObj, False)] TObj False, take 2 (lastN 3 args)))
    "prim__onCollectAny" => Just (Right (MkPrimSig "idr_on_collect" [(TObj, False), (TObj, False)] TObj False, take 2 (lastN 3 args)))
    "prim__os" => Just (Left (LStr "unix"))
    "prim__codegen" => Just (Left (LStr "lean"))
    _ => Nothing

||| Foreign functions that only have RefC/Scheme specs but which we implement
||| natively in the runtime.  (C name, uses Idris-side types)
||| Foreign functions that only have RefC specs, implemented natively in our
||| runtime (keyed by the RefC function name).  Some RefC functions are used at
||| several Idris types; those are resolved by the C return type in EmitC.
export
builtinForeign : List String -> Maybe String
builtinForeign ccs =
  case mapMaybe refc ccs of
    (f :: _) => lookupB f
    [] => Nothing
  where
    refc : String -> Maybe String
    refc s = if isPrefixOf "RefC:" s then Just (trim (substr 5 (length s) s)) else Nothing

    lookupB : String -> Maybe String
    lookupB f = case f of
      "fastPack" => Just "idr_fast_pack"
      "fastUnpack" => Just "idr_fast_unpack"
      "fastConcat" => Just "idr_fast_concat"
      "newBuffer" => Just "idr_buf_new"
      "getBufferSize" => Just "idr_buf_size"
      "getBufferUInt8" => Just "idr_buf_get_u8"
      "setBufferUInt8" => Just "idr_buf_set_u8"
      "getBufferByte" => Just "idr_buf_get_byte"
      "setBufferUInt16LE" => Just "idr_buf_set_u16"
      "getBufferUInt16LE" => Just "idr_buf_get_u16"
      "setBufferUInt32LE" => Just "idr_buf_set_u32"
      "getBufferUInt32LE" => Just "idr_buf_get_u32"
      "setBufferUInt64LE" => Just "idr_buf_set_u64"
      "getBufferUInt64LE" => Just "idr_buf_get_u64"
      "setBufferInt16LE" => Just "idr_buf_set_i16"
      "getBufferInt16LE" => Just "idr_buf_get_i16"
      "setBufferInt32LE" => Just "idr_buf_set_i32"
      "getBufferInt32LE" => Just "idr_buf_get_i32"
      "setBufferInt64LE" => Just "idr_buf_set_i64"
      "getBufferInt64LE" => Just "idr_buf_get_i64"
      "setBufferDouble" => Just "idr_buf_set_f64"
      "getBufferDouble" => Just "idr_buf_get_f64"
      "setBufferString" => Just "idr_buf_set_string"
      "getBufferString" => Just "idr_buf_get_string"
      "copyBuffer" => Just "idr_buf_copy"
      "clockTimeUtc" => Just "idr_clock_utc"
      "clockTimeMonotonic" => Just "idr_clock_monotonic"
      "clockTimeProcess" => Just "idr_clock_process"
      "clockTimeThread" => Just "idr_clock_thread"
      "clockTimeGcCpu" => Just "idr_clock_invalid"
      "clockTimeGcReal" => Just "idr_clock_invalid"
      "clockValid" => Just "idr_clock_valid"
      "clockSecond" => Just "idr_clock_second"
      "clockNanosecond" => Just "idr_clock_nanosecond"
      "stringIteratorNew" => Just "idr_strit_new"
      "stringIteratorToString" => Just "idr_strit_to_string"
      "stringIteratorNext" => Just "idr_strit_next"
      _ => Nothing
