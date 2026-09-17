import CORALean.ContSet.HPolytope.Real.Operations.Slab
import CORALean.ContSet.Interval.Float.Interval

/-!
# Halfspace descriptions over a floating-point scalar: the representation

CORA's `polytope` with `isHRep` set, its constraint matrices held in `𝕋`, and one
difference from the exact layer: the equality right-hand side is an `Interval`.

That is where rounding goes. An inequality absorbs its own by raising `b`, the
way an interval absorbs it into its bounds. An equality cannot — any rounding of
`Ae` or `be` names a different hyperplane, and a hyperplane has empty interior,
so the rounded set and the exact one generally meet in less than either. An
ambient error box does not rescue it either: the box is added after the
constraints have chosen a point, and a rounded equality system can be infeasible
where the exact one is not. The slack has to sit on the constraint, so `be` is an
interval and the row reads `Ae x ∈ be`.

The nominal reading is the exact layer's `slab`, so what this denotes is fixed by
definition rather than by a lemma, and every operation owes only enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure HPolytope (𝕋 : Type) (n : ℕ) where
  m : ℕ
  A : Mat 𝕋 m n
  b : Vec 𝕋 m
  me : ℕ
  Ae : Mat 𝕋 me n
  /-- Interval-valued, unlike the exact layer's point: this is where an
  equality's rounding goes. -/
  be : Interval 𝕋 me

def HPolytope.nominal [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 n) :
    CORALean.Real.HPolytope (Vec ℝ n) :=
  (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b)).intersection
    (Real.HPolytope.slab (toRealMat P.Ae) (toRealVec P.be.inf) (toRealVec P.be.sup))

def HPolytope.construct [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 n) : Set (Vec ℝ n) :=
  P.nominal.construct

/-! ## Storage

Every field is a function type, so the polytope an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here. -/

def HPolytope.materialise (P : HPolytope 𝕋 n) : HPolytope 𝕋 n :=
  let A : Vector (Vector 𝕋 n) P.m := Vector.ofFn fun i => Vector.ofFn fun j => P.A i j
  let b : Vector 𝕋 P.m := Vector.ofFn P.b
  let Ae : Vector (Vector 𝕋 n) P.me := Vector.ofFn fun i => Vector.ofFn fun j => P.Ae i j
  { m := P.m
    A := fun i j => (A[i.val]'i.isLt)[j.val]'j.isLt
    b := fun i => b[i.val]'i.isLt
    me := P.me
    Ae := fun i j => (Ae[i.val]'i.isLt)[j.val]'j.isLt
    be := P.be.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem HPolytope.materialise_eq (P : HPolytope 𝕋 n) : P.materialise = P := by
  simp [HPolytope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
