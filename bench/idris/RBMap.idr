module Main
import System
import Data.List

data Color = Red | Black
data Tree = Leaf | Node Color Tree Bits64 Bool Tree

balance1 : Tree -> Tree -> Tree
balance1 (Node _ _ kv vv t) (Node Red (Node Red l kx vx r1) ky vy r2) = Node Red (Node Black l kx vx r1) ky vy (Node Black r2 kv vv t)
balance1 (Node _ _ kv vv t) (Node Red l1 ky vy (Node Red l2 kx vx r)) = Node Red (Node Black l1 ky vy l2) kx vx (Node Black r kv vv t)
balance1 (Node _ _ kv vv t) (Node _ l ky vy r) = Node Black (Node Red l ky vy r) kv vv t
balance1 _ _ = Leaf

balance2 : Tree -> Tree -> Tree
balance2 (Node _ t kv vv _) (Node Red (Node Red l kx1 vx1 r1) ky vy r2) = Node Red (Node Black t kv vv l) kx1 vx1 (Node Black r1 ky vy r2)
balance2 (Node _ t kv vv _) (Node Red l1 ky vy (Node Red l2 kx2 vx2 r2)) = Node Red (Node Black t kv vv l1) ky vy (Node Black l2 kx2 vx2 r2)
balance2 (Node _ t kv vv _) (Node _ l ky vy r) = Node Black t kv vv (Node Red l ky vy r)
balance2 _ _ = Leaf

isRed : Tree -> Bool
isRed (Node Red _ _ _ _) = True
isRed _ = False

ins : Tree -> Bits64 -> Bool -> Tree
ins Leaf kx vx = Node Red Leaf kx vx Leaf
ins (Node Red a ky vy b) kx vx =
  if kx < ky then Node Red (ins a kx vx) ky vy b
  else if kx == ky then Node Red a kx vx b
  else Node Red a ky vy (ins b kx vx)
ins (Node Black a ky vy b) kx vx =
  if kx < ky then (if isRed a then balance1 (Node Black Leaf ky vy b) (ins a kx vx) else Node Black (ins a kx vx) ky vy b)
  else if kx == ky then Node Black a kx vx b
  else (if isRed b then balance2 (Node Black a ky vy Leaf) (ins b kx vx) else Node Black a ky vy (ins b kx vx))

setBlack : Tree -> Tree
setBlack (Node _ l k v r) = Node Black l k v r
setBlack e = e

insert : Tree -> Bits64 -> Bool -> Tree
insert t k v = if isRed t then setBlack (ins t k v) else ins t k v

fold : Tree -> Bits64 -> Bits64
fold Leaf acc = acc
fold (Node _ l _ v r) acc = fold r (fold l (if v then acc + 1 else acc))

mkMap : Bits64 -> Tree -> Tree
mkMap 0 m = m
mkMap n m = mkMap (n - 1) (insert m (n - 1) ((n - 1) `mod` 10 == 0))

main : IO ()
main = do
  args <- getArgs
  let n = case drop 1 args of { (a :: _) => cast (the Integer (cast a)) ; _ => 4200000 }
  printLn (fold (mkMap n Leaf) 0)
