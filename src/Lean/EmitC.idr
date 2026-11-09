||| C code generation from the IR, targeting Lean 4's runtime (lean.h)
module Lean.EmitC

import Core.Name
import Core.CompileExpr
import Compiler.Common
import Compiler.RefC.RefC
import Lean.IR
import Lean.Prims
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.List1
import Libraries.Data.String.Builder

%default covering

------------------------------------------------------------------------
-- Names

public export
record Names where
  constructor MkNames
  cnames : SortedMap Name String

export
mkNames : List Name -> Names
mkNames ns = MkNames (fst (foldl add (empty, empty) ns))
  where
    add : (SortedMap Name String, SortedSet String) -> Name -> (SortedMap Name String, SortedSet String)
    add (m, used) n =
      let base = "I_" ++ cName n
          c = if contains base used then base ++ "_" ++ show (length (SortedMap.toList m)) else base
      in (insert n c m, insert c used)

fname : Names -> Name -> String
fname ns n = fromMaybe ("I_" ++ cName n) (lookup n ns.cnames)

------------------------------------------------------------------------
-- Output monad

record EState where
  constructor MkEState
  out : Builder
  strLits : SortedMap String String     -- literal -> C name
  intLits : SortedMap Integer String    -- big Integer literal -> cache var
  boxed : SortedSet Name                -- functions needing a boxed wrapper
  litDecls : Builder

E : Type -> Type
E = State EState

emit : String -> E ()
emit s = modify (\st => { out := st.out <+> fromString s <+> char '\n' } st)

------------------------------------------------------------------------
-- Literals

hex2 : Int -> String
hex2 i = let h = "0123456789abcdef" in
         pack [ assert_total (strIndex h (i `div` 16)), assert_total (strIndex h (i `mod` 16)) ]

utf8 : Char -> List Int
utf8 c =
  let o = ord c in
  if o < 0x80 then [o]
  else if o < 0x800 then [0xC0 + o `div` 64, 0x80 + o `mod` 64]
  else if o < 0x10000 then [0xE0 + o `div` 4096, 0x80 + (o `div` 64) `mod` 64, 0x80 + o `mod` 64]
  else [0xF0 + o `div` 262144, 0x80 + (o `div` 4096) `mod` 64, 0x80 + (o `div` 64) `mod` 64, 0x80 + o `mod` 64]

||| C string literal (with byte count)
cStr : String -> (String, Nat)
cStr s =
  let bytes = concatMap utf8 (unpack s)
  in ("\"" ++ concatMap esc bytes ++ "\"", length bytes)
  where
    esc : Int -> String
    esc b = if b >= 32 && b < 127 && b /= 34 && b /= 92 && b /= 63
               then singleton (chr b)
               else "\\" ++ pack [chr (48 + b `div` 64), chr (48 + (b `div` 8) `mod` 8), chr (48 + b `mod` 8)]

strLit : String -> E String
strLit s =
  do st <- get
     case lookup s st.strLits of
       Just n => pure ("((lean_object*)&" ++ n ++ ")")
       Nothing =>
         do let n = "_lit_s" ++ show (length (SortedMap.toList st.strLits))
            let (cs, bytes) = cStr s
            let decl = "static lean_string_object " ++ n ++ " = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = LeanString}, .m_size = "
                       ++ show (bytes + 1) ++ ", .m_capacity = " ++ show (bytes + 1) ++ ", .m_length = "
                       ++ show (length s) ++ ", .m_data = " ++ cs ++ "};\n"
            put ({ strLits $= insert s n, litDecls $= (<+> fromString decl) } st)
            pure ("((lean_object*)&" ++ n ++ ")")

integerLit : Integer -> E String
integerLit i =
  if i >= -2147483647 && i <= 2147483647
     then pure ("lean_int64_to_int(" ++ show i ++ ")")
     else do st <- get
             n <- case lookup i st.intLits of
                    Just n => pure n
                    Nothing => do let n = "_lit_i" ++ show (length (SortedMap.toList st.intLits))
                                  put ({ intLits $= insert i n,
                                         litDecls $= (<+> fromString ("static lean_object* " ++ n ++ " = NULL;\n")) } st)
                                  pure n
             pure ("idr_integer_lit(\"" ++ show i ++ "\", &" ++ n ++ ")")

intLit : Integer -> Ty -> String
intLit i TI64 = if i == -9223372036854775808 then "INT64_MIN" else "INT64_C(" ++ show i ++ ")"
intLit i TU64 = "UINT64_C(" ++ show i ++ ")"
intLit i TF64 = show i ++ ".0"
intLit i t = "((" ++ cType t ++ ")" ++ show i ++ ")"

doubleLit : Double -> String
doubleLit d =
  if d /= d then "NAN"
  else if d == 1.0/0.0 then "INFINITY"
  else if d == -1.0/0.0 then "(-INFINITY)"
  else let s = show d in
       if isInfixOf "." s || isInfixOf "e" s then s else s ++ ".0"

------------------------------------------------------------------------
-- Expressions

var : Var -> String
var x = if x < 0 then "x_m" ++ show (negate x) else "x_" ++ show x

arg : Arg -> String
arg (AVar x) = var x
arg AIrr = "lean_box(0)"

boxFn : Ty -> String
boxFn TF64 = "lean_box_float"
boxFn t = "idr_box_" ++ tySuffix t

unboxFn : Ty -> String
unboxFn TF64 = "idr_unbox_f64"
unboxFn t = "idr_unbox_" ++ tySuffix t

record FnCtx where
  constructor MkFnCtx
  names : Names
  vtys : SortedMap Var Ty
  arities : SortedMap Name Nat
  self : Name
  selfParams : List Param
  jps : SortedMap Int (List Var)

vty : FnCtx -> Var -> Ty
vty ctx x = fromMaybe TObj (lookup x ctx.vtys)

sfield : String -> Nat -> Ty -> String
sfield z off t = "*(" ++ cType t ++ "*)((uint8_t*)lean_ctor_obj_cptr(" ++ z ++ ") + " ++ show off ++ ")"

setFields : String -> CtorInfo -> List Arg -> List String
setFields z c ys = zipWith set c.fields ys
  where
    set : Either Nat (Nat, Ty) -> Arg -> String
    set (Left i) y = "lean_ctor_set(" ++ z ++ ", " ++ show i ++ ", " ++ arg y ++ ");"
    set (Right (off, t)) y = sfield z off t ++ " = " ++ arg y ++ ";"

emitLet : FnCtx -> Var -> Ty -> Expr -> E ()
emitLet ctx z t e =
  let zs = var z in
  case e of
    ECtor c ys =>
      if isScalarCtor c then emit (zs ++ " = lean_box(" ++ show c.tag ++ ");")
      else do emit (zs ++ " = lean_alloc_ctor(" ++ show c.tag ++ ", " ++ show c.size ++ ", " ++ show c.ssize ++ ");")
              traverse_ emit (setFields zs c ys)
    EReset n x =>
      do emit ("if (lean_is_exclusive(" ++ var x ++ ")) {")
         traverse_ (\i => emit ("  lean_ctor_release(" ++ var x ++ ", " ++ show i ++ ");")) (take n [0..])
         emit ("  " ++ zs ++ " = " ++ var x ++ ";")
         emit "} else {"
         emit ("  lean_dec_ref(" ++ var x ++ ");")
         emit ("  " ++ zs ++ " = lean_box(0);")
         emit "}"
    EReuse w c u ys =>
      do emit ("if (lean_is_scalar(" ++ var w ++ ")) {")
         emit ("  " ++ zs ++ " = lean_alloc_ctor(" ++ show c.tag ++ ", " ++ show c.size ++ ", " ++ show c.ssize ++ ");")
         emit "} else {"
         emit ("  " ++ zs ++ " = " ++ var w ++ ";")
         when u $ emit ("  lean_ctor_set_tag(" ++ zs ++ ", " ++ show c.tag ++ ");")
         emit "}"
         traverse_ emit (setFields zs c ys)
    EProj i x => emit (zs ++ " = lean_ctor_get(" ++ var x ++ ", " ++ show i ++ ");")
    ESProj off ty x => emit (zs ++ " = " ++ sfield (var x) off ty ++ ";")
    EFap f ys => emit (zs ++ " = " ++ fname ctx.names f ++ "(" ++ joinBy ", " (map arg ys) ++ ");")
    EPap f ys =>
      do modify (\st => { boxed $= insert f } st)
         let ar = fromMaybe (length ys + 1) (lookup f ctx.arities)
         emit (zs ++ " = lean_alloc_closure((void*)" ++ fname ctx.names f ++ "_boxed, " ++ show ar ++ ", " ++ show (length ys) ++ ");")
         traverse_ (\(i, y) => emit ("lean_closure_set(" ++ zs ++ ", " ++ show i ++ ", " ++ arg y ++ ");")) (zip [0 .. length ys] ys)
    EAp f [y] => emit (zs ++ " = lean_apply_1(" ++ var f ++ ", " ++ arg y ++ ");")
    EAp f ys =>
      if length ys <= 16
         then emit (zs ++ " = lean_apply_" ++ show (length ys) ++ "(" ++ var f ++ ", " ++ joinBy ", " (map arg ys) ++ ");")
         else do emit ("{ lean_object* _args[] = {" ++ joinBy ", " (map arg ys) ++ "};")
                 emit ("  " ++ zs ++ " = lean_apply_m(" ++ var f ++ ", " ++ show (length ys) ++ ", _args); }")
    EBox ty x => emit (zs ++ " = " ++ boxFn ty ++ "(" ++ var x ++ ");")
    EUnbox ty x => emit (zs ++ " = " ++ unboxFn ty ++ "(" ++ var x ++ ");")
    ELit (LInt i ty) => emit (zs ++ " = " ++ intLit i ty ++ ";")
    ELit (LDouble d) => emit (zs ++ " = " ++ doubleLit d ++ ";")
    ELit (LStr s) => do l <- strLit s
                        emit (zs ++ " = " ++ l ++ ";")
    ELit (LTag i) => emit (zs ++ " = lean_box(" ++ show i ++ ");")
    ELit (LInteger i) => do l <- integerLit i
                            emit (zs ++ " = " ++ l ++ ";")
    EPrim sig ys => emit (zs ++ " = " ++ sig.cfun ++ "(" ++ joinBy ", " (map arg ys) ++ ");")
    ECast ty x =>
      if vty ctx x == TF64 && ty /= TF64
         then emit (zs ++ " = (" ++ cType ty ++ ")(int64_t)" ++ var x ++ ";")
         else emit (zs ++ " = (" ++ cType ty ++ ")" ++ var x ++ ";")
    ECopy x => emit (zs ++ " = " ++ var x ++ ";")
    EIsShared x => emit (zs ++ " = !lean_is_exclusive(" ++ var x ++ ");")

------------------------------------------------------------------------
-- Bodies

caseLitCond : FnCtx -> Var -> Lit -> E String
caseLitCond ctx x (LStr s) = do l <- strLit s
                                pure ("lean_string_dec_eq(" ++ var x ++ ", " ++ l ++ ")")
caseLitCond ctx x (LInteger i) = do l <- integerLit i
                                    pure ("idr_integer_eq(" ++ var x ++ ", " ++ l ++ ")")
caseLitCond ctx x (LDouble d) = pure (var x ++ " == " ++ doubleLit d)
caseLitCond ctx x (LTag i) = pure (var x ++ " == lean_box(" ++ show i ++ ")")
caseLitCond ctx x (LInt i t) = pure (var x ++ " == " ++ intLit i t)

isTailSelf : FnCtx -> Var -> Expr -> Body -> Bool
isTailSelf ctx z (EFap f ys) (BRet (AVar r)) = f == ctx.self && r == z && length ys == length ctx.selfParams
isTailSelf _ _ _ _ = False

mutual
  emitBody : FnCtx -> Body -> E ()
  emitBody ctx (BLet z t e b) =
    if isTailSelf ctx z e b
       then case e of
              EFap _ ys => emitTailCall ctx ys
              _ => pure ()
       else do emitLet ctx z t e
               emitBody ctx b
  emitBody ctx (BJp j ps jb rest) =
    do emitBody ctx rest
       emit ("block_" ++ show j ++ ": ;")
       emitBody ctx jb
  emitBody ctx (BCase x ty alts) =
    case alts of
      [ACtor _ b] => emitBody ctx b
      [ADefault b] => emitBody ctx b
      (ACtor _ _ :: _) =>
        do emit ("switch (lean_obj_tag(" ++ var x ++ ")) {")
           traverse_ (emitCtorAlt ctx) alts
           unless (any isDefault alts) $ emit "default: __builtin_unreachable();"
           emit "}"
      _ => if isScalar ty && ty /= TF64
              then do emit ("switch (" ++ var x ++ ") {")
                      traverse_ (emitSwitchAlt ctx) alts
                      unless (any isDefault alts) $ emit "default: __builtin_unreachable();"
                      emit "}"
              else emitIfChain ctx x alts
  emitBody ctx (BRet a) =
    case a of
      AVar x => emit ("return " ++ var x ++ ";")
      AIrr => emit "return lean_box(0);"
  emitBody ctx (BJmp j ys) =
    do traverse_ (\(y, x) => emit (var x ++ " = " ++ arg y ++ ";")) (zip ys (fromMaybe [] (lookup j ctx.jps)))
       emit ("goto block_" ++ show j ++ ";")
  emitBody ctx (BUnreach msg) =
    if msg == "" then emit "__builtin_unreachable();"
    else do emit ("idr_crash_cstr(" ++ fst (cStr msg) ++ ");")
  emitBody ctx (BInc x n b) =
    do emit (if n == 1 then "lean_inc(" ++ var x ++ ");" else "lean_inc_n(" ++ var x ++ ", " ++ show n ++ ");")
       emitBody ctx b
  emitBody ctx (BDec x b) = do emit ("lean_dec(" ++ var x ++ ");")
                               emitBody ctx b
  emitBody ctx (BDel x b) = do emit ("lean_free_object(" ++ var x ++ ");")
                               emitBody ctx b
  emitBody ctx (BSetTag x t b) = do emit ("lean_ctor_set_tag(" ++ var x ++ ", " ++ show t ++ ");")
                                    emitBody ctx b
  emitBody ctx (BSet x i a b) = do emit ("lean_ctor_set(" ++ var x ++ ", " ++ show i ++ ", " ++ arg a ++ ");")
                                   emitBody ctx b
  emitBody ctx (BSSet x n off ty y b) =
    do emit (sfield (var x) off ty ++ " = " ++ var y ++ ";")
       emitBody ctx b
  emitBody ctx (BRelease x i b) = do emit ("lean_ctor_release(" ++ var x ++ ", " ++ show i ++ ");")
                                     emitBody ctx b

  emitTailCall : FnCtx -> List Arg -> E ()
  emitTailCall ctx ys =
    do -- parallel assignment through temporaries
       let ps = ctx.selfParams
       let changed = filter (\(p, y) => arg y /= var p.pvar) (zip ps ys)
       case changed of
         [] => pure ()
         [(p, y)] => emit (var p.pvar ++ " = " ++ arg y ++ ";")
         _ => do emit "{"
                 traverse_ (\(i, (p, y)) => emit (cType p.pty ++ " _t" ++ show i ++ " = " ++ arg y ++ ";")) (zip [0 .. length changed] changed)
                 traverse_ (\(i, (p, y)) => emit (var p.pvar ++ " = _t" ++ show i ++ ";")) (zip [0 .. length changed] changed)
                 emit "}"
       emit "goto _start;"

  isDefault : Alt -> Bool
  isDefault (ADefault _) = True
  isDefault _ = False

  emitCtorAlt : FnCtx -> Alt -> E ()
  emitCtorAlt ctx (ACtor c b) = do emit ("case " ++ show c.tag ++ ": {")
                                   emitBody ctx b
                                   emit "}"
  emitCtorAlt ctx (ADefault b) = do emit "default: {"
                                    emitBody ctx b
                                    emit "}"
  emitCtorAlt ctx (ALit _ b) = pure ()

  emitSwitchAlt : FnCtx -> Alt -> E ()
  emitSwitchAlt ctx (ALit (LInt i t) b) = do emit ("case " ++ intLit i t ++ ": {")
                                             emitBody ctx b
                                             emit "}"
  emitSwitchAlt ctx (ADefault b) = do emit "default: {"
                                      emitBody ctx b
                                      emit "}"
  emitSwitchAlt ctx _ = pure ()

  emitIfChain : FnCtx -> Var -> List Alt -> E ()
  emitIfChain ctx x [] = emit "__builtin_unreachable();"
  emitIfChain ctx x (ADefault b :: _) = do emit "{"
                                           emitBody ctx b
                                           emit "}"
  emitIfChain ctx x (ALit l b :: rest) =
    do c <- caseLitCond ctx x l
       emit ("if (" ++ c ++ ") {")
       emitBody ctx b
       emit "} else {"
       emitIfChain ctx x rest
       emit "}"
  emitIfChain ctx x (ACtor _ b :: rest) = emitIfChain ctx x rest

------------------------------------------------------------------------
-- Collect variable types (and jump parameter lists)

collectVars : Body -> List (Var, Ty)
collectVars (BLet x t _ b) = (x, t) :: collectVars b
collectVars (BJp _ ps jb r) = map (\p => (p.pvar, p.pty)) ps ++ collectVars jb ++ collectVars r
collectVars (BCase _ _ alts) = concatMap (collectVars . altBody) alts
collectVars (BInc _ _ b) = collectVars b
collectVars (BDec _ b) = collectVars b
collectVars (BDel _ b) = collectVars b
collectVars (BSetTag _ _ b) = collectVars b
collectVars (BSet _ _ _ b) = collectVars b
collectVars (BSSet _ _ _ _ _ b) = collectVars b
collectVars (BRelease _ _ b) = collectVars b
collectVars _ = []

||| Join point parameters (needed to emit jumps)
collectJps : Body -> List (Int, List Var)
collectJps (BLet _ _ _ b) = collectJps b
collectJps (BJp j ps jb r) = (j, map pvar ps) :: collectJps jb ++ collectJps r
collectJps (BCase _ _ alts) = concatMap (collectJps . altBody) alts
collectJps (BInc _ _ b) = collectJps b
collectJps (BDec _ b) = collectJps b
collectJps (BDel _ b) = collectJps b
collectJps (BSetTag _ _ b) = collectJps b
collectJps (BSet _ _ _ b) = collectJps b
collectJps (BSSet _ _ _ _ _ b) = collectJps b
collectJps (BRelease _ _ b) = collectJps b
collectJps _ = []

||| Functions used in partial applications (they need boxed wrappers)
collectPaps : Body -> List Name
collectPaps (BLet _ _ (EPap f _) b) = f :: collectPaps b
collectPaps (BLet _ _ _ b) = collectPaps b
collectPaps (BJp _ _ jb r) = collectPaps jb ++ collectPaps r
collectPaps (BCase _ _ alts) = concatMap (collectPaps . altBody) alts
collectPaps (BInc _ _ b) = collectPaps b
collectPaps (BDec _ b) = collectPaps b
collectPaps (BDel _ b) = collectPaps b
collectPaps (BSetTag _ _ b) = collectPaps b
collectPaps (BSet _ _ _ b) = collectPaps b
collectPaps (BSSet _ _ _ _ _ b) = collectPaps b
collectPaps (BRelease _ _ b) = collectPaps b
collectPaps _ = []

------------------------------------------------------------------------
-- Declarations

paramList : List Param -> String
paramList [] = "void"
paramList ps = joinBy ", " (map (\p => cType p.pty ++ " " ++ var p.pvar) ps)

protoOf : Names -> Decl -> String
protoOf ns d = "static " ++ cType d.ret ++ " " ++ fname ns d.name ++ "(" ++ paramList d.params ++ ")"

protoImpl : Names -> Decl -> String
protoImpl ns d = "static " ++ cType d.ret ++ " " ++ fname ns d.name ++ "_impl(" ++ paramList d.params ++ ")"

-- FFI ------------------------------------------------------------------

ffiCType : CFType -> String
ffiCType CFUnit = "void"
ffiCType CFInt = "int64_t"
ffiCType CFInt8 = "int8_t"
ffiCType CFInt16 = "int16_t"
ffiCType CFInt32 = "int32_t"
ffiCType CFInt64 = "int64_t"
ffiCType CFUnsigned8 = "uint8_t"
ffiCType CFUnsigned16 = "uint16_t"
ffiCType CFUnsigned32 = "uint32_t"
ffiCType CFUnsigned64 = "uint64_t"
ffiCType CFString = "char*"
ffiCType CFDouble = "double"
ffiCType CFChar = "char"
ffiCType (CFIORes t) = ffiCType t
ffiCType _ = "void*"

isWorld : CFType -> Bool
isWorld CFWorld = True
isWorld _ = False

ffiArg : (Var, CFType) -> String
ffiArg (v, CFString) = "(char*)lean_string_cstr(" ++ var v ++ ")"
ffiArg (v, CFPtr) = "idr_unbox_ptr(" ++ var v ++ ")"
ffiArg (v, CFGCPtr) = "idr_unbox_ptr(" ++ var v ++ ")"
ffiArg (v, CFBuffer) = "(void*)lean_sarray_cptr(" ++ var v ++ ")"
ffiArg (v, CFForeignObj) = "idr_unbox_ptr(" ++ var v ++ ")"
ffiArg (v, CFInteger) = "idr_integer_to_i64(" ++ var v ++ ")"
ffiArg (v, CFFun _ _) = "NULL /* callbacks unsupported */"
ffiArg (v, CFUnit) = "0"
ffiArg (v, t) = case cfTyIsObj t of
                  True => "idr_unbox_ptr(" ++ var v ++ ")"
                  False => var v
  where
    cfTyIsObj : CFType -> Bool
    cfTyIsObj (CFStruct _ _) = True
    cfTyIsObj (CFUser _ _) = True
    cfTyIsObj _ = False

ffiRet : CFType -> String -> String
ffiRet CFString r = "idr_str_of_cstr(" ++ r ++ ")"
ffiRet CFUnit r = "lean_box(0)"
ffiRet CFInteger r = "idr_integer_of_i64(" ++ r ++ ")"
ffiRet (CFIORes t) r = ffiRet t r
ffiRet t r = if ffiCType t == "void*" then "idr_box_ptr(" ++ r ++ ")" else r

unitRet : CFType -> Bool
unitRet CFUnit = True
unitRet (CFIORes t) = unitRet t
unitRet _ = False

||| the Scheme function names of the foreign specs ("scheme:f", "scheme,chez:f")
schemeNames : List String -> List String
schemeNames [] = []
schemeNames (c :: cs) =
  case break (== ':') c of
    (targets, rest) =>
      if ("scheme" `elem` map trim (forget (split (== ',') targets))) && rest /= ""
         then trim (substr 1 (length rest) rest) :: schemeNames cs
         else schemeNames cs

schemeBuiltin : String -> Maybe (String, Nat)
schemeBuiltin f = case f of
  "blodwen-thread-wait" => Just ("idr_thread_wait", 1)
  "blodwen-set-thread-data" => Just ("idr_set_thread_data", 1)
  "blodwen-get-thread-data" => Just ("idr_get_thread_data", 0)
  "get-thread-id" => Just ("idr_get_thread_id", 0)
  "blodwen-make-mutex" => Just ("idr_mutex_new", 0)
  "blodwen-mutex-acquire" => Just ("idr_mutex_acquire", 1)
  "blodwen-mutex-release" => Just ("idr_mutex_release", 1)
  "blodwen-make-condition" => Just ("idr_cond_new", 0)
  "blodwen-condition-wait" => Just ("idr_cond_wait", 2)
  "blodwen-condition-wait-timeout" => Just ("idr_cond_wait_timeout", 3)
  "blodwen-condition-signal" => Just ("idr_cond_signal", 1)
  "blodwen-condition-broadcast" => Just ("idr_cond_broadcast", 1)
  "blodwen-make-semaphore" => Just ("idr_sem_new", 1)
  "blodwen-semaphore-post" => Just ("idr_sem_post", 1)
  "blodwen-semaphore-wait" => Just ("idr_sem_wait", 1)
  "blodwen-make-barrier" => Just ("idr_barrier_new", 1)
  "blodwen-barrier-wait" => Just ("idr_barrier_wait", 1)
  "blodwen-make-channel" => Just ("idr_chan_new", 0)
  "blodwen-channel-get" => Just ("idr_chan_get", 1)
  "blodwen-channel-get-non-blocking" => Just ("idr_chan_get_nb", 1)
  "blodwen-channel-get-with-timeout" => Just ("idr_chan_get_timeout", 2)
  "blodwen-channel-put" => Just ("idr_chan_put", 2)
  "blodwen-make-future" => Just ("idr_future_new", 1)
  "blodwen-await-future" => Just ("idr_future_await", 1)
  _ => Nothing

emitForeign : Names -> Decl -> List String -> List CFType -> CFType -> E ()
emitForeign ns d ccs fargs ret =
  do let vs = zip (map pvar d.params) fargs
     let realArgs = filter (not . isWorld . snd) vs
     let cOverride = case parseCC ["C"] ccs of
                       Just (_, f :: _) => case trim f of
                                             "strlen" => Just "idr_str_bytelen"
                                             "refc_fork" => Just "idr_fork"
                                             _ => Nothing
                       _ => Nothing
     -- functions with only Scheme specs that we implement natively
     -- (C function, number of trailing runtime arguments it takes)
     let schemeOnly = choiceMap schemeBuiltin (schemeNames ccs)
     let nreal = length realArgs
     let builtin = if isJust (parseCC ["C"] ccs) then map (\f => (f, nreal)) cOverride
                   else map (\f => (f, nreal)) (builtinForeign ccs) <|> schemeOnly
     case builtin of
       Just (cf, n) =>
         do emit (protoOf ns d ++ " {")
            let used = drop (minus nreal n) realArgs
            emit ("  return " ++ cf ++ "(" ++ joinBy ", " (map (var . fst) used) ++ ");")
            emit "}"
       Nothing =>
         case parseCC ["C"] ccs of
           Just (_, cfun :: _) =>
             do let alias = "idr_ffi_" ++ cName d.name
                emit ("extern " ++ ffiCType ret ++ " " ++ alias ++ "(" ++ (case realArgs of
                                                                          [] => "void"
                                                                          _ => joinBy ", " (map (ffiCType . snd) realArgs)) ++ ") __asm__(\"" ++ trim cfun ++ "\");")
                emit (protoOf ns d ++ " {")
                let call = alias ++ "(" ++ joinBy ", " (map ffiArg realArgs) ++ ")"
                if unitRet ret
                   then do emit ("  " ++ call ++ ";")
                           emit "  return lean_box(0);"
                   else emit ("  return " ++ ffiRet ret call ++ ";")
                emit "}"
           _ =>
             do emit (protoOf ns d ++ " {")
                emit ("  idr_crash_cstr(\"unsupported foreign function " ++ show d.name ++ "\");")
                emit "}"

-- boxed wrappers -----------------------------------------------------

boxedProto : Names -> Decl -> String
boxedProto ns d =
  let n = length d.params
      fn = fname ns d.name in
  if n > 16
     then "static lean_object* " ++ fn ++ "_boxed(lean_object** _a)"
     else "static lean_object* " ++ fn ++ "_boxed(" ++ joinBy ", " (map (\i => "lean_object* _a" ++ show i) (take n [0..])) ++ ")"

emitBoxed : Names -> Decl -> E ()
emitBoxed ns d =
  do let n = length d.params
     let fn = fname ns d.name
     emit (boxedProto ns d ++ " {")
     let argN : Nat -> String
         argN i = if n > 16 then "_a[" ++ show i ++ "]" else "_a" ++ show i
     let args = zipWith (\i, p => if isScalar p.pty then unboxFn p.pty ++ "(" ++ argN i ++ ")" else argN i) [0 .. n] d.params
     emit ("  " ++ cType d.ret ++ " _r = " ++ fn ++ "(" ++ joinBy ", " args ++ ");")
     -- closure arguments are owned: release those the function only borrows,
     -- and boxed scalars (which may be heap allocated)
     traverse_ (\(i, p) => when (p.borrow || isScalar p.pty) $ emit ("  lean_dec(" ++ argN i ++ ");"))
               (zip [0 .. n] d.params)
     if isScalar d.ret
        then emit ("  return " ++ boxFn d.ret ++ "(_r);")
        else emit "  return _r;"
     emit "}"

emitDecl : Names -> SortedMap Name Nat -> SortedSet Name -> Decl -> E ()
emitDecl ns ars cafs d =
  case d.kind of
    Foreign ccs fargs ret => emitForeign ns d ccs fargs ret
    Normal =>
      do let vars = collectVars d.body
         let ctx = MkFnCtx ns (fromList (map (\p => (p.pvar, p.pty)) d.params ++ vars)) ars d.name d.params
                           (fromList (collectJps d.body))
         let isCaf = contains d.name cafs
         when isCaf $
           do emit (protoImpl ns d ++ ";")
              emit (protoOf ns d ++ " {")
              emit "  static lean_object* _cache = NULL;"
              emit ("  if (LEAN_UNLIKELY(_cache == NULL)) { _cache = " ++ fname ns d.name ++ "_impl(); lean_mark_persistent(_cache); }")
              emit "  return _cache;"
              emit "}"
         emit ((if isCaf then protoImpl ns d else protoOf ns d) ++ " {")
         -- declare locals, grouped by type
         let locals = nubBy (\a, b => fst a == fst b) vars
         traverse_ (\(x, t) => emit (cType t ++ " " ++ var x ++ ";")) locals
         emit "_start: ;"
         emitBody ctx d.body
         emit "}"

------------------------------------------------------------------------
-- Program

export
emitProgram : List Decl -> Name -> SortedSet Name -> String
emitProgram ds mainName cafs =
  let names = mkNames (map name ds)
      ars = fromList (map (\d => (d.name, length d.params)) ds)
      st = execState (MkEState neutral empty empty empty neutral) (genAll names ars)
  in build (fromString "#include \"idris_lean.h\"\n\n"
            <+> st.litDecls <+> fromString "\n"
            <+> st.out)
  where
    genAll : Names -> SortedMap Name Nat -> E ()
    genAll names ars =
      do traverse_ (\d => emit (protoOf names d ++ ";")) ds
         let paps = SortedSet.fromList (concatMap (\d => collectPaps d.body) ds)
         let boxedDecls = filter (\d => contains d.name paps) ds
         traverse_ (\d => emit (boxedProto names d ++ ";")) boxedDecls
         emit ""
         traverse_ (emitDecl names ars cafs) ds
         traverse_ (emitBoxed names) boxedDecls
         emit ""
         emit ("static lean_object* idr_main_thunk(void) {")
         case find (\d => d.name == mainName) ds of
           Just d => if isScalar d.ret
                        then emit ("  " ++ fname names mainName ++ "(); return lean_box(0);")
                        else emit ("  return " ++ fname names mainName ++ "();")
           Nothing => emit "  return lean_box(0);"
         emit "}"
         emit "int main(int argc, char **argv) { return idr_run_main(argc, argv, idr_main_thunk); }"
