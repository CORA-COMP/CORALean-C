import CORALean.ContSet.Interval.Float.Operations.Intersection

/-!
# `Interval.intersection` is exact, over a floating-point scalar

Nothing rounds: choosing the larger of two stored lower bounds, or the smaller
of two upper ones, returns one of them, so the intersection is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.intersection_exact (I₁ I₂ : Interval 𝕋 n) :
    (I₁.intersection I₂).construct = I₁.construct ∩ I₂.construct := by -- --- PROOF ---
  have key : ∀ (x : Vec ℝ n) (j : Fin n),
      (toReal (maximum (I₁.inf j) (I₂.inf j)) ≤ x j
        ∧ x j ≤ toReal (minimum (I₁.sup j) (I₂.sup j)))
      ↔ ((toReal (I₁.inf j) ≤ x j ∧ x j ≤ toReal (I₁.sup j))
        ∧ (toReal (I₂.inf j) ≤ x j ∧ x j ≤ toReal (I₂.sup j))) := by
    intro x j
    rw [toReal_maximum, toReal_minimum, max_le_iff, le_min_iff]
    tauto
  -- `max` of the lower ends against `min` of the upper ones is exactly meeting both boxes
  ext x
  constructor
  · intro h
    exact ⟨fun j => ((key x j).mp (h j)).1, fun j => ((key x j).mp (h j)).2⟩
  · rintro ⟨h₁, h₂⟩ j
    exact (key x j).mpr ⟨h₁ j, h₂ j⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
