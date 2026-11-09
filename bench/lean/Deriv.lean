inductive Expr
  | val : Int64 → Expr
  | var : UInt64 → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Expr → Expr
  | ln  : Expr → Expr

open Expr

partial def pown : Int64 → Int64 → Int64
  | _, 0 => 1
  | a, n => let b := pown a (n / 2); b * b * (if n % 2 == 0 then 1 else a)

partial def mkAdd : Expr → Expr → Expr
  | val n, val m => val (n + m)
  | val 0, f => f
  | f, val 0 => f
  | f, val n => mkAdd (val n) f
  | val n, Expr.add (val m) f => mkAdd (val (n+m)) f
  | f, Expr.add (val n) g => mkAdd (val n) (mkAdd f g)
  | Expr.add f g, h => mkAdd f (mkAdd g h)
  | f, g => Expr.add f g

partial def mkMul : Expr → Expr → Expr
  | val n, val m => val (n*m)
  | val 0, _ => val 0
  | _, val 0 => val 0
  | val 1, f => f
  | f, val 1 => f
  | f, val n => mkMul (val n) f
  | val n, Expr.mul (val m) f => mkMul (val (n*m)) f
  | f, Expr.mul (val n) g => mkMul (val n) (mkMul f g)
  | Expr.mul f g, h => mkMul f (mkMul g h)
  | f, g => Expr.mul f g

def mkPow : Expr → Expr → Expr
  | val m, val n => val (pown m n)
  | _, val 0 => val 1
  | f, val 1 => f
  | val 0, _ => val 0
  | f, g => Expr.pow f g

def mkLn : Expr → Expr
  | val 1 => val 0
  | f => Expr.ln f

def d (x : UInt64) : Expr → Expr
  | val _ => val 0
  | var y => if x == y then val 1 else val 0
  | Expr.add f g => mkAdd (d x f) (d x g)
  | Expr.mul f g => mkAdd (mkMul f (d x g)) (mkMul g (d x f))
  | Expr.pow f g => mkMul (mkPow f g) (mkAdd (mkMul (mkMul g (d x f)) (mkPow f (val (-1)))) (mkMul (mkLn f) (d x g)))
  | Expr.ln f => mkMul (d x f) (mkPow f (val (-1)))

def count : Expr → UInt64
  | val _ => 1
  | var _ => 1
  | Expr.add f g => count f + count g
  | Expr.mul f g => count f + count g
  | Expr.pow f g => count f + count g
  | Expr.ln f => count f

def nest (f : Expr → Expr) : Nat → Expr → Expr
  | 0, x => x
  | n+1, x => nest f n (f x)

def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let x := var 0
  let f := mkPow x x
  let r := nest (fun e => d 0 e) n f
  IO.println (count r)
