import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Theorems.PlusExact

/-!
# `Interval.plus` contains the Minkowski sum

Nothing about sums of sets appears here — `Real` has already proved that. The
whole obligation is that each bound rounded the right way.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_plus_outer_refines (I₁ I₂ : Interval 𝕋 n) :
    (I₁.nominal.plus I₂.nominal).construct ⊆ (I₁.plus I₂).construct := by
  intro x hx i
  exact ⟨le_trans (addDown_le_add _ _) (hx i).1, le_trans (hx i).2 (add_le_addUp _ _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.plus_outer (I₁ I₂ : Interval 𝕋 n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  subset_trans (Real.Interval.plus_outer I₁.nominal I₂.nominal)
    (Interval.aux_plus_outer_refines I₁ I₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
