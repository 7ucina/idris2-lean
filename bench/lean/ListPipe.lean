partial def build (n : UInt64) (acc : List UInt64) : List UInt64 :=
  if n == 0 then acc else build (n-1) ((n-1) :: acc)

def step (xs : List UInt64) : List UInt64 :=
  (xs.map (fun x => x * 3 + 1)).filter (fun x => x % 7 != 0)

def iter : Nat → List UInt64 → List UInt64
  | 0, xs => xs
  | k+1, xs => iter k (step xs |>.map (· % 1000003))

def sumL : List UInt64 → UInt64 → UInt64
  | [], a => a
  | x :: xs, a => sumL xs (a + x)

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000000").toNat!.toUInt64
  IO.println (sumL (iter 50 (build n [])) 0)
