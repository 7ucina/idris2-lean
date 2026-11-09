module Main
import System
import Data.List

build : Bits64 -> List Bits64 -> List Bits64
build 0 acc = acc
build n acc = build (n - 1) ((n - 1) :: acc)

step : List Bits64 -> List Bits64
step xs = filter (\x => x `mod` 7 /= 0) (map (\x => x * 3 + 1) xs)

iter : Nat -> List Bits64 -> List Bits64
iter Z xs = xs
iter (S k) xs = iter k (map (\x => x `mod` 1000003) (step xs))

sumL : List Bits64 -> Bits64 -> Bits64
sumL [] a = a
sumL (x :: xs) a = sumL xs (a + x)

main : IO ()
main = do
  args <- getArgs
  let n = case drop 1 args of { (a :: _) => cast (the Integer (cast a)) ; _ => 1000000 }
  printLn (sumL (iter 50 (build n [])) 0)
