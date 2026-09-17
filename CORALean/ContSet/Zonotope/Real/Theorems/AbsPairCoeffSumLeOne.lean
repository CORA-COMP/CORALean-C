import CORALean.ContSet.Zonotope.Real.Theorems.AbsWeightedLe
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffSum

/-!
# The paired-sum coefficient is admissible

Over a column both blocks have, the two halves are bounded by `λ` and `1 - λ`,
which sum to one. Past the shorter block only the first half is there, and its
weight is already at most one.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h₁ h₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.abs_pairCoeffSum_le_one {β₁ : Fin h₁ → ℝ} {β₂ : Fin h₂ → ℝ} {lam : ℝ}
    (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (j : Fin h₁) : |Zonotope.pairCoeffSum β₁ β₂ lam j| ≤ 1 := by -- --- PROOF ---
  simp only [Zonotope.pairCoeffSum]
  by_cases hj : (j : ℕ) < h₂
  · rw [dif_pos hj]
    have hA := Zonotope.abs_weighted_le hl0 (hβ₁ j)
    have hB := Zonotope.abs_weighted_le (by linarith : (0:ℝ) ≤ 1 - lam) (hβ₂ ⟨j, hj⟩)
    rw [abs_le] at hA hB ⊢
    constructor <;> linarith
  · rw [dif_neg hj]
    exact le_trans (Zonotope.abs_weighted_le hl0 (hβ₁ j)) hl1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
