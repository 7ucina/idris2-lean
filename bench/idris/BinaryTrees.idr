module Main
import System
import Data.List
import Data.Bits

data Tree = Leaf | Node Tree Tree

make : Bits64 -> Tree
make d = if d == 0 then Node Leaf Leaf else Node (make (d - 1)) (make (d - 1))

check : Tree -> Bits64
check Leaf = 0
check (Node l r) = 1 + check l + check r

sumChecks : Bits64 -> Bits64 -> Bits64 -> Bits64
sumChecks 0 d acc = acc
sumChecks i d acc = sumChecks (i - 1) d (acc + check (make d))

loopDepths : Bits64 -> Bits64 -> Bits64 -> IO ()
loopDepths d maxD minD =
  if d > maxD then pure () else do
    let iters = prim__shl_Bits64 1 (maxD - d + minD)
    let c = sumChecks iters d 0
    putStrLn (show iters ++ "\t trees of depth " ++ show d ++ "\t check: " ++ show c)
    loopDepths (d + 2) maxD minD

main : IO ()
main = do
  args <- getArgs
  let n : Bits64 = case drop 1 args of { (a :: _) => cast (the Integer (cast a)) ; _ => 21 }
  let maxD = max 6 n
  putStrLn ("stretch tree of depth " ++ show (maxD + 1) ++ "\t check: " ++ show (check (make (maxD + 1))))
  let long = make maxD
  loopDepths 4 maxD 4
  putStrLn ("long lived tree of depth " ++ show maxD ++ "\t check: " ++ show (check long))
