inductive Color | red | black
inductive Tree | leaf | node (c : Color) (l : Tree) (k : UInt64) (v : Bool) (r : Tree)

def balance1 : Tree → Tree → Tree
  | .node _ _ kv vv t, .node .red (.node .red l kx vx r₁) ky vy r₂ => .node .red (.node .black l kx vx r₁) ky vy (.node .black r₂ kv vv t)
  | .node _ _ kv vv t, .node .red l₁ ky vy (.node .red l₂ kx vx r) => .node .red (.node .black l₁ ky vy l₂) kx vx (.node .black r kv vv t)
  | .node _ _ kv vv t, .node _ l ky vy r => .node .black (.node .red l ky vy r) kv vv t
  | _, _ => .leaf

def balance2 : Tree → Tree → Tree
  | .node _ t kv vv _, .node .red (.node .red l kx₁ vx₁ r₁) ky vy r₂ => .node .red (.node .black t kv vv l) kx₁ vx₁ (.node .black r₁ ky vy r₂)
  | .node _ t kv vv _, .node .red l₁ ky vy (.node .red l₂ kx₂ vx₂ r₂) => .node .red (.node .black t kv vv l₁) ky vy (.node .black l₂ kx₂ vx₂ r₂)
  | .node _ t kv vv _, .node _ l ky vy r => .node .black t kv vv (.node .red l ky vy r)
  | _, _ => .leaf

def isRed : Tree → Bool
  | .node .red .. => true
  | _ => false

def ins : Tree → UInt64 → Bool → Tree
  | .leaf, kx, vx => .node .red .leaf kx vx .leaf
  | .node .red a ky vy b, kx, vx =>
    if kx < ky then .node .red (ins a kx vx) ky vy b
    else if kx == ky then .node .red a kx vx b
    else .node .red a ky vy (ins b kx vx)
  | .node .black a ky vy b, kx, vx =>
    if kx < ky then (if isRed a then balance1 (.node .black .leaf ky vy b) (ins a kx vx) else .node .black (ins a kx vx) ky vy b)
    else if kx == ky then .node .black a kx vx b
    else (if isRed b then balance2 (.node .black a ky vy .leaf) (ins b kx vx) else .node .black a ky vy (ins b kx vx))

def setBlack : Tree → Tree
  | .node _ l k v r => .node .black l k v r
  | e => e

def insert (t : Tree) (k : UInt64) (v : Bool) : Tree :=
  if isRed t then setBlack (ins t k v) else ins t k v

def fold : Tree → UInt64 → UInt64
  | .leaf, acc => acc
  | .node _ l _ v r, acc => fold r (fold l (if v then acc + 1 else acc))

partial def mkMap (n : UInt64) (m : Tree) : Tree :=
  if n == 0 then m else mkMap (n-1) (insert m (n-1) ((n-1) % 10 == 0))

def main (args : List String) : IO Unit := do
  let n := (args.headD "4200000").toNat!.toUInt64
  IO.println (fold (mkMap n .leaf) 0)
