import CORALean.ContSet.Zonotope.Float.API
import CORALean.ContSet.Interval.Float.API
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
import CORALean.Global.Float.Instances.Dyadic.API
import CoraleanC.IEEE
import Lean.Data.Json

/-!
# One CORA-COMP instance, run on CORALean's float layer

`coralean-c <params> <results file>` runs the instance `params` describes (the
`instances.csv` JSON) and writes its verdict. Every operation it times is a
CORALean definition, compiled to C by Lean, at the scalar `CORALEAN_SCALAR`
names: `dyadic` (default), CORALean's `Dyadic 53`, or `double`, the hardware
double rounded outward (`CoraleanC.IEEE`). Only generating the inputs and
drawing points happen here, since they are not set operations and carry no
guarantee.
-/

namespace CoraleanC

open CORALean CORALean.Float FloatOps Lean

/-- A double's mantissa width, so rounding happens where CORA's doubles round. -/
abbrev D := Dyadic 53

/-- What the driver needs of a scalar beyond CORALean's classes. -/
class Number (𝕋 : Type) where
  ofFloat : Float → 𝕋
  /-- Whether the value is one the scalar's guarantees speak about. -/
  finite : 𝕋 → Bool
  dtype : String

open Number


-- ========================================  RANDOMNESS  ======================================== --

/-- splitmix64: statistically adequate for inputs, and cheap enough to not dominate
`generateRandom`. Over `IO`, so the inputs are generated before the clock starts
rather than wherever the compiler places a pure computation. -/
abbrev Rand := StateT UInt64 IO

def nextU64 : Rand UInt64 := modifyGet fun (s : UInt64) =>
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- Uniform on `[0, 1)`, from the top 53 bits. -/
def uniform : Rand Float := do
  return ((← nextU64) >>> 11).toFloat / 9007199254740992.0

def randn : Rand Float := do
  let u₁ := 1 - (← uniform)
  let u₂ ← uniform
  return Float.sqrt (-2 * Float.log u₁) * Float.cos (6.283185307179586 * u₂)

def randnArray (k : Nat) : Rand (Array Float) := do
  let mut a := Array.mkEmpty k
  for _ in [0:k] do a := a.push (← randn)
  return a

/-- Exact: a finite double is a dyadic with a 53-bit mantissa. -/
def dyadicOfFloat (x : Float) : D :=
  if x == 0 then ⟨0, 0⟩ else
  let (m, e) := x.frExp
  let k : Int := (m.abs.scaleB 53).toUInt64.toNat
  ⟨if m < 0 then -k else k, e - 53⟩

instance : Number D where
  ofFloat := dyadicOfFloat
  finite _ := true
  dtype := "dyadic53"

instance : Number Float where
  ofFloat := id
  finite := IEEE.isFinite
  dtype := "float64-outward"

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [Number 𝕋]

def vecOf (a : Array 𝕋) (n : Nat) : Vec 𝕋 n := fun i => a.getD i.val zero


-- ========================================  RANDOM SETS  ======================================= --

/-- CORA's `interval.generateRandom`: centre `U[-2, 2]`, radius `R·u/2`. -/
def randomInterval (n : Nat) : Rand (Interval 𝕋 n) := do
  let mut lo := Array.mkEmpty n
  let mut hi := Array.mkEmpty n
  for _ in [0:n] do
    let c := 4 * (← uniform) - 2
    let r := 10 * (← uniform) * (← uniform) / 2
    lo := lo.push (ofFloat (c - r))
    hi := hi.push (ofFloat (c + r))
  return Interval.materialise ⟨vecOf lo n, vecOf hi n⟩

/-- CORA's `zonotope.generateRandom`: centre `10·randn`, each generator a uniform
unit direction scaled by `U[0, 1]`. -/
def randomZonotope (n m : Nat) : Rand (Zonotope 𝕋 n) := do
  let c ← randnArray n
  let mut cols : Array (Array 𝕋) := Array.mkEmpty m
  for _ in [0:m] do
    let d ← randnArray n
    let len := (← uniform) / Float.sqrt (d.foldl (fun s x => s + x * x) 0)
    cols := cols.push (d.map fun x => ofFloat (len * x))
  let Z : Zonotope 𝕋 n :=
    { h := m
      c := vecOf (c.map ofFloat) n
      G := fun i j => (cols.getD j.val #[]).getD i.val zero
      E := ⟨fun _ => zero, fun _ => zero⟩ }
  return Z.materialise

def randomMatrix (n : Nat) : Rand (Mat 𝕋 n n) := do
  let rows ← (List.range n).mapM fun _ => return (← randnArray n).map ofFloat
  let rows := rows.toArray
  let M : Vector (Vector 𝕋 n) n := Vector.ofFn fun i => Vector.ofFn fun j =>
    (rows.getD i.val #[]).getD j.val zero
  return fun i j => (M[i.val]'i.isLt)[j.val]'j.isLt

/-- A uniformly random unit direction, the query of `supportFunc`. -/
def randomDirection (n : Nat) : Rand (Vec 𝕋 n) := do
  let d ← randnArray n
  let len := Float.sqrt (d.foldl (fun s x => s + x * x) 0)
  return vecOf (d.map fun x => ofFloat (x / len)) n


-- ==========================================  POINTS  ========================================== --

def store {n : Nat} (p : Vec 𝕋 n) : Vec 𝕋 n :=
  let v : Vector 𝕋 n := Vector.ofFn p
  fun i => v[i.val]'i.isLt

/-- `randPoint` `standard`: `c + G·β`, `β ~ U[-1, 1]^m`. -/
def pointZ {n : Nat} (Z : Zonotope 𝕋 n) : Rand (Vec 𝕋 n) := do
  let mut β := Array.mkEmpty Z.h
  for _ in [0:Z.h] do β := β.push (ofFloat (2 * (← uniform) - 1))
  let b := vecOf β Z.h
  return store fun i => addDown (Z.c i) (dotDown (fun j => Z.G i j) b)

/-- Uniform in the box. Rounded down from `inf` by less than the width rounded down,
so the point stays inside the stored bounds. -/
def pointI {n : Nat} (I : Interval 𝕋 n) : Rand (Vec 𝕋 n) := do
  let mut u := Array.mkEmpty n
  for _ in [0:n] do u := u.push (ofFloat (← uniform))
  return store fun i => addDown (I.inf i) (mulDown (u.getD i.val zero) (subDown (I.sup i) (I.inf i)))

def points {α : Type} (k : Nat) (draw : Rand α) : Rand (Array α) := do
  let mut a := Array.mkEmpty k
  for _ in [0:k] do a := a.push (← draw)
  return a


-- ========================================  OPERATIONS  ======================================== --

/-- The functional `x ↦ dᵀx`, as the one-row matrix `rowLin` reads. -/
abbrev dirLin {n : Nat} (d : Vec 𝕋 n) := rowLin (q := 1) (Matrix.of fun _ => d) 0

def supportZ {n : Nat} (Z : Zonotope 𝕋 n) (d : Vec 𝕋 n) : 𝕋 :=
  (Z.boundDot (c := dirLin d) d fun _ => rfl).val

def supportI {n : Nat} (I : Interval 𝕋 n) (d : Vec 𝕋 n) : 𝕋 :=
  (I.boundDot (c := dirLin d) d fun _ => rfl).val

/-- A `true` is sound, since `le` only ever answers `true` for an order that holds. -/
def containsI {n : Nat} (I : Interval 𝕋 n) (p : Vec 𝕋 n) : Bool :=
  (List.finRange n).all fun i => le (I.inf i) (p i) && le (p i) (I.sup i)

/-- `(zeros(n), eye(n))`, the least a tool can build: what `test` measures. -/
def unitZonotope (n : Nat) : Zonotope 𝕋 n :=
  Zonotope.materialise
    { h := n
      c := fun _ => zero
      G := fun i j => if i.val = j.val then one else zero
      E := ⟨fun _ => zero, fun _ => zero⟩ }


-- =========================================  INSTANCE  ========================================= --

structure Params where
  set : String
  operation : String
  dim : Nat
  generators : Nat
  device : String
  repetition : Nat
  batchSize : Nat
  points : Nat

/-- By hand: the optional fields default here, which derived `FromJson` would not do. -/
def Params.parse (s : String) : Except String Params := do
  let j ← Json.parse s
  let opt (k : String) : Except String Nat := return (j.getObjValAs? Nat k).toOption.getD 0
  return {
    set := ← j.getObjValAs? String "set"
    operation := ← j.getObjValAs? String "operation"
    dim := ← j.getObjValAs? Nat "dim"
    generators := ← opt "generators"
    device := ← j.getObjValAs? String "device"
    repetition := ← j.getObjValAs? Nat "repetition"
    batchSize := max 1 (← opt "batch_size")
    points := ← opt "points" }

def operations : List String :=
  ["startup", "generateRandom", "randPoint", "supportFunc", "matMul", "minkSum", "contains"]

def unsupportedReason (p : Params) : Option String :=
  if p.device != "cpu" then some s!"device {p.device}: CORALean runs on the CPU only"
  else if p.set != "zonotope" && p.set != "interval" then some s!"set {p.set}"
  else if p.set == "zonotope" && p.operation == "contains" then
    some "zonotope point containment: CORALean has no float decision procedure for it"
  else if !operations.contains p.operation then some s!"operation {p.operation}"
  else none

def nanosSince (t : Nat) : IO Float := do
  return ((← IO.monoNanosNow) - t).toFloat / 1e9

/-- Runs `f` `k` times, keeping each result behind an effect so the compiler cannot
drop the unused computation, and returns the last. -/
def repeatOp {α : Type} (k : Nat) (f : Unit → α) : IO (Option α) := do
  let sink ← IO.mkRef (none : Option α)
  for _ in [0:k] do sink.set (some (f ()))
  sink.get

def allFin (k : Nat) (f : Fin k → Bool) : Bool := (List.finRange k).all f

def finiteV {n : Nat} (v : Vec 𝕋 n) : Bool := allFin n fun i => finite (v i)

def finiteI {n : Nat} (I : Interval 𝕋 n) : Bool := finiteV I.inf && finiteV I.sup

def finiteZ {n : Nat} (Z : Zonotope 𝕋 n) : Bool :=
  finiteV Z.c && finiteI Z.E && allFin n fun i => allFin Z.h fun j => finite (Z.G i j)

/-- Whether the last repetition's results are all ones the guarantees cover. -/
def checked {α : Type} (last : Option (Array α)) (ok : α → Bool) : Bool :=
  (last.getD #[]).all ok

def repeatRand {α : Type} (k : Nat) (seed : UInt64) (f : Rand α) : IO Unit := do
  let sink ← IO.mkRef (none : Option α)
  for _ in [0:k] do sink.set (some (← f.run' seed))

/-- Generates the inputs, then returns the timed repetitions, which answer whether
every result is covered by the guarantees: finite, and every containment proved. -/
def prepare (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [Number 𝕋] (p : Params) :
    Rand (IO Bool) := do
  let n := p.dim
  let b := p.batchSize
  let rep := p.repetition
  let batch {α : Type} (g : Rand α) : Rand (Array α) := points b g
  match p.set, p.operation with
  | _, "startup" => return do discard <| repeatOp rep fun _ => unitZonotope (𝕋 := 𝕋) n; return true
  | "zonotope", "generateRandom" =>
    -- the operation is the generation itself, so the seed is all it takes as input
    let seed ← nextU64
    return do repeatRand rep seed (batch (randomZonotope (𝕋 := 𝕋) n p.generators)); return true
  | "interval", "generateRandom" =>
    let seed ← nextU64
    return do repeatRand rep seed (batch (randomInterval (𝕋 := 𝕋) n)); return true
  | "zonotope", "randPoint" =>
    let Zs ← batch (randomZonotope (𝕋 := 𝕋) n p.generators)
    let seed ← nextU64
    return do repeatRand rep seed (Zs.mapM fun Z => points p.points (pointZ Z)); return true
  | "interval", "randPoint" =>
    let Is ← batch (randomInterval (𝕋 := 𝕋) n)
    let seed ← nextU64
    return do repeatRand rep seed (Is.mapM fun I => points p.points (pointI I)); return true
  | "zonotope", "supportFunc" =>
    let Zs ← batch (randomZonotope (𝕋 := 𝕋) n p.generators)
    let ds ← batch (randomDirection (𝕋 := 𝕋) n)
    return do
      let last ← repeatOp rep fun _ => Zs.zipWith (fun Z d => supportZ Z d) ds
      return checked last finite
  | "interval", "supportFunc" =>
    let Is ← batch (randomInterval (𝕋 := 𝕋) n)
    let ds ← batch (randomDirection (𝕋 := 𝕋) n)
    return do
      let last ← repeatOp rep fun _ => Is.zipWith (fun I d => supportI I d) ds
      return checked last finite
  | "zonotope", "matMul" =>
    let M ← randomMatrix (𝕋 := 𝕋) n
    let Zs ← batch (randomZonotope (𝕋 := 𝕋) n p.generators)
    return do
      let last ← repeatOp rep fun _ => Zs.map fun Z => (Zonotope.mtimes M Z).materialise
      return checked last finiteZ
  | "interval", "matMul" =>
    let M ← randomMatrix (𝕋 := 𝕋) n
    let Is ← batch (randomInterval (𝕋 := 𝕋) n)
    return do
      let last ← repeatOp rep fun _ => Is.map fun I => (Interval.mtimes M I).materialise
      return checked last finiteI
  | "zonotope", "minkSum" =>
    let Z₁ ← batch (randomZonotope (𝕋 := 𝕋) n p.generators)
    let Z₂ ← batch (randomZonotope (𝕋 := 𝕋) n p.generators)
    return do
      let last ← repeatOp rep fun _ => Z₁.zipWith (fun A B => (A.plus B).materialise) Z₂
      return checked last finiteZ
  | "interval", "minkSum" =>
    let I₁ ← batch (randomInterval (𝕋 := 𝕋) n)
    let I₂ ← batch (randomInterval (𝕋 := 𝕋) n)
    return do
      let last ← repeatOp rep fun _ => I₁.zipWith (fun A B => (A.plus B).materialise) I₂
      return checked last finiteI
  | "interval", "contains" =>
    let Is ← batch (randomInterval (𝕋 := 𝕋) n)
    let Ps ← Is.mapM fun I => points p.points (pointI I)
    return do
      let ok ← IO.mkRef true
      for _ in [0:rep] do
        ok.set ((Is.zipWith (fun I P => P.all (containsI I)) Ps).all id)
      ok.get
  | _, _ => return pure false

def writeResult (path : System.FilePath) (verdict : String) (extra : List (String × String)) :
    IO Unit :=
  IO.FS.writeFile path <|
    ",".intercalate ("result" :: extra.map (·.1)) ++ "\n" ++
    ",".intercalate (verdict :: extra.map (·.2)) ++ "\n"

def runAt (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [Number 𝕋] (p : Params)
    (out : System.FilePath) : IO Unit := do
  let t₀ ← IO.monoNanosNow
  let seed := (← IO.monoNanosNow).toUInt64
  let op ← (prepare 𝕋 p).run' seed
  let tGen ← nanosSince t₀
  let t₁ ← IO.monoNanosNow
  let covered ← op
  let tOp ← nanosSince t₁
  let extra := [("time_generate", toString tGen), ("time_operation", toString tOp),
    ("dtype", dtype 𝕋)]
  if covered then
    writeResult out "finished" extra
  else if p.operation == "contains" then
    IO.println "[coralean-c] a containment query was not proved"
    writeResult out "error" extra
  else
    IO.println "[coralean-c] a result is not finite, so no guarantee covers it"
    writeResult out "error" extra

def run (json : String) (out : System.FilePath) : IO Unit := do
  let p ← IO.ofExcept (Params.parse json)
  if let some why := unsupportedReason p then
    IO.println s!"[coralean-c] unsupported: {why}"
    writeResult out "unsupported" []
    return
  match (← IO.getEnv "CORALEAN_SCALAR").getD "dyadic" with
  | "dyadic" => runAt D p out
  | "double" => runAt Float p out
  | other => throw <| IO.userError s!"CORALEAN_SCALAR={other}: expected dyadic or double"

end CoraleanC

def main (args : List String) : IO UInt32 := do
  match args with
  | [params, out] =>
    try
      CoraleanC.run params out
      return 0
    catch e =>
      IO.eprintln s!"[coralean-c] {e}"
      CoraleanC.writeResult out "error" []
      return 1
  | _ =>
    IO.eprintln "usage: coralean-c <params json> <results file>"
    return 2
