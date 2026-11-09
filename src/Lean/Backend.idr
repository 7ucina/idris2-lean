||| The `lean` code generator: Idris2 -> C on top of Lean 4's runtime
module Lean.Backend

import Core.Context
import Core.Core
import Core.Directory
import Core.Name
import Compiler.Common
import Compiler.ANF
import Idris.Syntax
import Lean.IR
import Lean.Lower
import Lean.Types
import Lean.RC
import Lean.Opt
import Lean.ResetReuse
import Lean.Borrow
import Lean.Expand
import Lean.CSE
import Lean.Layout
import Lean.Spec
import Lean.Accum
import Data.SortedSet
import Lean.EmitC
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.String
import System
import System.File
import System.Directory
import Libraries.Utils.Path

%default covering

getEnvOr : String -> String -> IO String
getEnvOr v def = pure (fromMaybe def !(getEnv v))

||| Directory layout (overridable through environment variables)
record Paths where
  constructor MkPaths
  leanHome : String
  support : String
  idrisLib : String
  cc : String
  cflags : String

getPaths : IO Paths
getPaths =
  do home <- getEnvOr "HOME" "/root"
     let base = home ++ "/idris2-fast"
     lean <- getEnvOr "IDRIS2_LEAN_HOME" (base ++ "/lean/lean-4.35.0-linux")
     sup <- getEnvOr "IDRIS2_LEAN_SUPPORT" (base ++ "/idris2-lean/support")
     lib <- getEnvOr "IDRIS2_LEAN_IDRIS_LIB" (base ++ "/prefix/idris2-0.8.0/lib")
     cc <- getEnvOr "IDRIS2_LEAN_CC" (lean ++ "/bin/clang")
     cflags <- getEnvOr "IDRIS2_LEAN_CFLAGS" "-O3"
     pure (MkPaths lean sup lib cc cflags)

dumpIR : String -> List Decl -> Core ()
dumpIR file ds =
  do Right () <- coreLift $ writeFile file (unlines (map showDecl ds))
       | Left err => throw (InternalError ("cannot write " ++ file))
     pure ()

removeAtL : Nat -> List a -> List a
removeAtL _ [] = []
removeAtL Z (_ :: xs) = xs
removeAtL (S k) (x :: xs) = x :: removeAtL k xs

||| declared representation of a specialised clone (inherits its original's)
cloneDecl : SortedMap Name (List Ty, Ty) -> (Name, (Name, Nat, Nat)) -> Maybe (Name, (List (Maybe Ty), Maybe Ty))
cloneDecl dmap (n, (orig, i, ncaps)) =
  do (ps, r) <- lookup orig dmap
     pure (n, (map Just (removeAtL i ps) ++ replicate ncaps Nothing, Just r))

isConDef : (Name, ANFDef) -> Bool
isConDef (_, MkACon _ _ _) = True
isConDef _ = False

export
compileProgram : {auto c : Ref Ctxt Defs} -> List (Name, ANFDef) -> String -> Core ()
compileProgram defs outBase =
  do ftys <- traverse (\(n, _) => do t <- ctorFieldTys n
                                     pure (map (\ts => (n, ts)) t))
                      (filter isConDef defs)
     let g = mkGlobalInfo (fromList (catMaybes ftys)) defs
     let decls0 = mapMaybe (lowerDef g) defs
     dump <- coreLift (getEnv "IDRIS2_LEAN_DUMP")
     when (isJust dump) $ dumpIR (outBase ++ ".lower.ir") decls0
     let (declsSp, origins) = specialise decls0
     when (isJust dump) $ dumpIR (outBase ++ ".spec.ir") declsSp
     let declsS = map simplify declsSp
     -- declared representations from the typechecked context
     dsigs <- traverse (\d => case d.kind of
                                Normal => do r <- fnSig d.name (length d.params)
                                             pure (map (\x => (d.name, x)) r)
                                _ => pure Nothing) decls0
     let dmap : SortedMap Name (List Ty, Ty) = fromList (catMaybes dsigs)
     let declared : Declared
           = fromList (map (\(n, (ps, r)) => (n, (map Just ps, Just r))) (SortedMap.toList dmap)
                       ++ mapMaybe (cloneDecl dmap) (SortedMap.toList origins))
     let sigs = inferSigs declared declsS
     let decls1t = map (simplify . applyTypes sigs) declsS
     let pures = pureFunctions decls1t
     noAcc <- coreLift (getEnv "IDRIS2_LEAN_NO_ACCUM")
     let accum = if isJust noAcc then id else accumulate
     let decls1 = map simplify (accum (map (simplify . cseDecl pures) decls1t))
     when (isJust dump) $ dumpIR (outBase ++ ".typed.ir") decls1
     let decls1r = map insertResetReuse decls1
     let mainName = MN "__mainExpression" 0
     let decls1b = inferBorrow (== mainName) decls1r
     when (isJust dump) $ dumpIR (outBase ++ ".borrow.ir") decls1b
     let borrowMap : SortedMap Name (List Bool) = fromList (map (\d => (d.name, map borrow d.params)) decls1b)
     let decls2 = map (explicitRC (\n => lookup n borrowMap)) decls1b
     let decls3 = map (\d => { body $= cancelIncDec } d) decls2
     when (isJust dump) $ dumpIR (outBase ++ ".rc.ir") decls3
     let decls4 = map expandResetReuse decls3
     when (isJust dump) $ dumpIR (outBase ++ ".final.ir") decls4
     let cafs = fromList (map name (filter (\d => length d.params == 0 && isObj d.ret
                                                  && contains d.name pures && d.name /= mainName) decls4))
     let src = emitProgram decls4 mainName cafs
     Right () <- coreLift $ writeFile (outBase ++ ".c") src
       | Left err => throw (InternalError ("cannot write " ++ outBase ++ ".c"))
     pure ()

compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c s tmpDir outputDir tm outfile =
  do cdata <- getCompileData False ANF tm
     let outBase = outputDir </> outfile
     compileProgram (anf cdata) outBase
     p <- coreLift getPaths
     useLld <- coreLift (exists (p.support ++ "/ld/ld.lld"))
     let bundledClang = p.cc == p.leanHome ++ "/bin/clang"
     usePch <- coreLift (exists (p.support ++ "/idris_lean.h.pch"))
     let sysinc = if bundledClang
                    then " -nostdinc -isystem " ++ p.leanHome ++ "/include/clang"
                         ++ " -isystem /usr/include/x86_64-linux-gnu -isystem /usr/include"
                    else ""
     let pch = if bundledClang && usePch then " -include-pch " ++ p.support ++ "/idris_lean.h.pch" else ""
     -- compile with the chosen C compiler, link with the system gcc (+ lld)
     let ccmd = p.cc ++ " " ++ p.cflags ++ " -DNDEBUG -w" ++ sysinc
                ++ " -I" ++ p.support ++ " -I" ++ p.leanHome ++ "/include" ++ pch
                ++ " -c " ++ outBase ++ ".c -o " ++ outBase ++ ".o"
     let cmd = ccmd ++ " && gcc" ++ (if useLld then " -B" ++ p.support ++ "/ld -fuse-ld=lld -Wl,--gc-sections" else "")
               ++ " " ++ outBase ++ ".o " ++ p.support ++ "/libidris_lean.a"
               ++ " -o " ++ outBase
               ++ " -L" ++ p.idrisLib ++ " -L" ++ p.leanHome ++ "/lib/lean -L" ++ p.leanHome ++ "/lib"
               ++ " -Wl,-Bstatic -lidris2_support -Wl,-Bdynamic"
               ++ " -Wl,--start-group -lInit -lleanrt -Wl,--end-group"
               ++ " -Wl,-Bstatic -lc++ -lc++abi -lgmp -luv -Wl,-Bdynamic -lpthread -ldl -lrt -lm"
     0 <- coreLift $ system cmd
       | _ => do coreLift $ putStrLn ("C compilation failed: " ++ cmd)
                 pure Nothing
     pure (Just outBase)

executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (execDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm =
  do Just exe <- compileExpr c s tmpDir tmpDir tm "_tmp_lean"
       | Nothing => pure ()
     ignore $ coreLift $ system exe

export
codegenLean : Codegen
codegenLean = MkCG compileExpr executeExpr Nothing Nothing
