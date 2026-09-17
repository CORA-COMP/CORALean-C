import CORALean.ContSet.Zonotope.Real.Theorems.AbsWeightedLe
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffDiff

/-!
# The paired-difference coefficient is admissible

The mirror of the sum bound, and a separate proof because the surplus branch
differs: past the shorter block it is the second block's weight that is left,
not the first's.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h₁ h₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the difference coefficient, the mirror of the sum one
theorem Zonotope.abs_pairCoeffDiff_le_one {β₁ : Fin h₁ → ℝ} {β₂ : Fin h₂ → ℝ} {lam : ℝ}
    (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (j : Fin h₂) : |Zonotope.pairCoeffDiff β₁ β₂ lam j| ≤ 1 := by -- --- PROOF ---
  simp only [Zonotope.pairCoeffDiff]
  by_cases hj : (j : ℕ) < h₁
  · rw [dif_pos hj]
    have hA := Zonotope.abs_weighted_le hl0 (hβ₁ ⟨j, hj⟩)
    have hB := Zonotope.abs_weighted_le (by linarith : (0:ℝ) ≤ 1 - lam) (hβ₂ j)
    rw [abs_le] at hA hB ⊢
    constructor <;> linarith
  · rw [dif_neg hj]
    exact le_trans (Zonotope.abs_weighted_le (by linarith : (0:ℝ) ≤ 1 - lam) (hβ₂ j))
      (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
