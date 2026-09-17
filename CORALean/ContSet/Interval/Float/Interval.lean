import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.ContSet.Interval.Real.Interval

/-!
# Intervals over a floating-point scalar: the representation

CORA's `interval` with the same `inf` and `sup`, held in `𝕋` rather than ℝ.

What it denotes is the exact layer's `construct` of `nominal`, fixed by
definition rather than by a lemma. Each operation then owes only enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Interval (𝕋 : Type) (n : ℕ) where
  inf : Vec 𝕋 n
  sup : Vec 𝕋 n

def Interval.nominal [SoundFloatArithmetic 𝕋] (I : Interval 𝕋 n) :
    CORALean.Real.Interval (Vec ℝ n) :=
  ⟨toRealVec I.inf, toRealVec I.sup⟩

def Interval.construct [SoundFloatArithmetic 𝕋] (I : Interval 𝕋 n) : Set (Vec ℝ n) :=
  I.nominal.construct

/-! ## Storage

Both bounds are function types, so the interval an operation returns is a
closure over the one it was given and a loop pays for its whole history on every
read. `materialise` stores them, and `materialise_eq` says it is the identity,
so what it changes is only what running a definition costs. `Global/Tensor` says
why the vectors are built here rather than by a helper.

This is also the storage of five other representations, which carry an error box
of this type and materialise it through here. -/

def Interval.materialise (I : Interval 𝕋 n) : Interval 𝕋 n :=
  let lo : Vector 𝕋 n := Vector.ofFn I.inf
  let hi : Vector 𝕋 n := Vector.ofFn I.sup
  ⟨fun i => lo[i.val]'i.isLt, fun i => hi[i.val]'i.isLt⟩

omit [FloatOps 𝕋] in
@[simp] theorem Interval.materialise_eq (I : Interval 𝕋 n) : I.materialise = I := by
  simp [Interval.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
