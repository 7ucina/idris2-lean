module Main
import System
import Data.List
import Data.String

nfib : Bits64 -> Bits64
nfib n = if n < 2 then 1 else nfib (n - 1) + nfib (n - 2) + 1

main : IO ()
main = do
  args <- getArgs
  let n = case drop 1 args of { (a :: _) => cast (the Integer (cast a)) ; _ => 38 }
  printLn (nfib n)
