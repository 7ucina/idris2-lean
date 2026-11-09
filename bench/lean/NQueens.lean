def safe (q : Int64) : Int64 → List Int64 → Bool
  | _, [] => true
  | d, c :: cs => q != c && q != c + d && q != c - d && safe q (d+1) cs

def gen (n : Int64) : Nat → List (List Int64)
  | 0 => [[]]
  | k+1 => (gen n k).foldr (fun b acc =>
      (List.range n.toNatClampNeg).foldr (fun qn acc' =>
        let q := (qn.toInt64) + 1
        if safe q 1 b then (q :: b) :: acc' else acc') acc) []

def main (args : List String) : IO Unit := do
  let n := (args.headD "13").toNat!
  IO.println (gen n.toInt64 n).length
