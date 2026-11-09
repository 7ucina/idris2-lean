module Main
import System
import Data.List

safe : Int64 -> Int64 -> List Int64 -> Bool
safe q d [] = True
safe q d (c :: cs) = q /= c && q /= c + d && q /= c - d && safe q (d + 1) cs

range : Int64 -> Int64 -> List Int64
range i n = if i >= n then [] else i :: range (i + 1) n

gen : Int64 -> Nat -> List (List Int64)
gen n Z = [[]]
gen n (S k) = foldr (\b, acc => foldr (\qn, acc' => let q = qn + 1 in if safe q 1 b then (q :: b) :: acc' else acc') acc (range 0 n)) [] (gen n k)

main : IO ()
main = do
  args <- getArgs
  let n = case drop 1 args of { (a :: _) => cast (the Integer (cast a)) ; _ => 13 }
  printLn (length (gen (cast n) n))
