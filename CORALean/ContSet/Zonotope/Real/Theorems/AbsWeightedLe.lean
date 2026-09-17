import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A weighted coefficient reaches no further than its weight

The one arithmetic step behind both paired-coefficient bounds: since the two
weights of a convex combination sum to one, bounding each half by its own weight
is what makes their sum land back in `[-1,1]`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A weighted coefficient reaches no further than its weight. -/
theorem Zonotope.abs_weighted_le {b w : ℝ} (hw : 0 ≤ w) (hb : |b| ≤ 1) : |w * b| ≤ w := by
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
