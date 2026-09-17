import CORALean.ContSet.Interval.Real.Interval

/-!
# Scaling stays between the scaled endpoints

Where `min` and `max` absorb the sign of the scale: for a negative one the two
endpoints swap roles, and taking the extremes of the pair is what makes the one
statement cover both. Every interval product in the tree reduces to this,
whether the other factor is a matrix entry or an interval matrix's.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Scaling a point between two endpoints lands between the scaled endpoints,
whichever way the scale points. -/
theorem Interval.mul_between_endpoints {c lo hi x : ℝ} (h₁ : lo ≤ x) (h₂ : x ≤ hi) :
    min (c * lo) (c * hi) ≤ c * x ∧ c * x ≤ max (c * lo) (c * hi) := by -- --- PROOF ---
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h₁ hc),
           (mul_le_mul_of_nonneg_left h₂ hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h₂ hc),
           (mul_le_mul_of_nonpos_left h₁ hc).trans (le_max_left _ _)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
