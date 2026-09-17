import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A zonotope is convex

The affine image of a cube, so a weighted average of two points is the image of
the same average of their coefficients — which is still a coefficient, `[-1,1]`
being convex.

What an integral valued in the set needs, and a property only some
representations have — unlike `linComb`, stated so a non-convex one can make it.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.convex_construct (Z : Zonotope α) : Convex ℝ Z.construct := by -- --- PROOF ---
  rintro x ⟨β₁, hβ₁, rfl⟩ y ⟨β₂, hβ₂, rfl⟩ a b ha hb hab
  refine ⟨fun j => a * β₁ j + b * β₂ j, fun j => ?_, ?_⟩
  · refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith [hβ₁ j, hβ₂ j, abs_nonneg (β₁ j), abs_nonneg (β₂ j)]
  · have hsum : ∑ j, (a * β₁ j + b * β₂ j) • Z.G j
        = a • (∑ j, β₁ j • Z.G j) + b • ∑ j, β₂ j • Z.G j := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [add_smul, smul_smul, smul_smul]
    calc a • (Z.c + ∑ j, β₁ j • Z.G j) + b • (Z.c + ∑ j, β₂ j • Z.G j)
        = (a + b) • Z.c + (a • (∑ j, β₁ j • Z.G j) + b • ∑ j, β₂ j • Z.G j) := by
          rw [smul_add, smul_add, add_smul]; abel
      _ = Z.c + ∑ j, (a * β₁ j + b * β₂ j) • Z.G j := by rw [hab, one_smul, hsum]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
