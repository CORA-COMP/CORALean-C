import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# The coefficient hits its target

The other half of what makes `coefficient` a witness: scaled back up by the
generator radius it returns the target exactly. At `R = 0` the hypothesis pins
`D` to zero, which is what keeps the degenerate branch honest.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mul_coefficient {R D : ℝ} (hDR : |D| ≤ R) :
    R * Zonotope.coefficient R D = D := by -- --- PROOF ---
  rw [Zonotope.coefficient]
  by_cases h0 : R = 0
  · simp only [h0, if_pos, zero_mul]
    exact (abs_eq_zero.mp (le_antisymm (h0 ▸ hDR) (abs_nonneg _))).symm
  · rw [if_neg h0]; field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
