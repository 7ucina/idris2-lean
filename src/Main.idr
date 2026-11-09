module Main

import Compiler.Common
import Idris.Driver
import Lean.Backend

main : IO ()
main = mainWithCodegens [("lean", codegenLean)]
