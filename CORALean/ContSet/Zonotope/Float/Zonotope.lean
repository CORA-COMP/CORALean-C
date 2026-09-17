import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Zonotopes over a floating-point scalar: the representation

CORA's `zonotope` with its centre and generator matrix, plus the error box that
makes it an `InflatedContSet`. The nominal part is the zonotope those stored
floats describe; the box holds what rounding has cost.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Zonotope (𝕋 : Type) (n : ℕ) where
  h : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Zonotope 𝕋 n) (CORALean.Real.Zonotope (Vec ℝ n)) 𝕋 n where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal Z := ⟨Z.h, toRealVec Z.c, fun j i => toReal (Z.G i j)⟩
  error Z := Z.E

/-! The nominal zonotope's fields, so proofs can see through the instance. -/

theorem Zonotope.nominal_h [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).h = Z.h := rfl

theorem Zonotope.nominal_c [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).c = toRealVec Z.c := rfl

theorem Zonotope.nominal_G [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).G = fun j i => toReal (Z.G i j) := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Zonotope.construct [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct Z

/-! ## Storage

Every field is a function type, so the zonotope an operation returns is a closure
over the one it was given, and a loop that iterates operations pays for its whole
history on every entry read. `materialise` stores the four fields; it is the
identity, which `materialise_eq` states and every proof downstream rewrites with,
so what it changes is only what running the definition costs. `Global/Tensor`
says why the vectors are built here rather than by a helper.

`Instances.lean` is where it is applied — an algorithm reaches a representation
through the operation classes and nowhere else, so materialising there bounds
every loop at once without a single operation or guarantee knowing about it. -/

def Zonotope.materialise (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  let c : Vector 𝕋 n := Vector.ofFn Z.c
  let G : Vector (Vector 𝕋 Z.h) n := Vector.ofFn fun i => Vector.ofFn fun j => Z.G i j
  { h := Z.h
    c := fun i => c[i.val]'i.isLt
    G := fun i j => (G[i.val]'i.isLt)[j.val]'j.isLt
    E := Z.E.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem Zonotope.materialise_eq (Z : Zonotope 𝕋 n) : Z.materialise = Z := by
  simp [Zonotope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
