inductive Tree | leaf | node (l r : Tree)
deriving Inhabited

partial def make (d : UInt64) : Tree :=
  if d == 0 then .node .leaf .leaf else .node (make (d-1)) (make (d-1))

def check : Tree → UInt64
  | .leaf => 0
  | .node l r => 1 + check l + check r

partial def loopDepths (d maxD minD : UInt64) : IO Unit := do
  if d > maxD then return
  let iters : UInt64 := 1 <<< (maxD - d + minD)
  let mut c : UInt64 := 0
  for _ in [0:iters.toNat] do
    c := c + check (make d)
  IO.println s!"{iters}\t trees of depth {d}\t check: {c}"
  loopDepths (d+2) maxD minD

def main (args : List String) : IO Unit := do
  let n := (args.headD "21").toNat!.toUInt64
  let maxD := max 6 n
  IO.println s!"stretch tree of depth {maxD+1}\t check: {check (make (maxD+1))}"
  let long := make maxD
  loopDepths 4 maxD 4
  IO.println s!"long lived tree of depth {maxD}\t check: {check long}"
