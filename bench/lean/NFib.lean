partial def nfib (n : UInt64) : UInt64 :=
  if n < 2 then 1 else nfib (n-1) + nfib (n-2) + 1

def main (args : List String) : IO Unit := do
  let n := (args.headD "38").toNat!
  IO.println (nfib n.toUInt64)
