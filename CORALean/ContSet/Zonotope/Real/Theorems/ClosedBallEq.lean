import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The coefficient cube is a closed ball

The coefficients a zonotope quantifies over are exactly `Metric.closedBall 0 1`
in the supremum norm on `Fin h → ℝ`. Stated on its own because two proofs need
the rewriting in opposite directions: `isCompact_construct` turns the cube into
a ball to apply `isCompact_closedBall`, and `ConZonotope.isCompact_domain` turns
the ball back into the cube to bound its domain by it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The coefficient cube, as a ball, which is the form `isCompact_closedBall`
speaks about. -/
theorem Zonotope.closedBall_eq (h : ℕ) :
    Metric.closedBall (0 : Fin h → ℝ) 1 = {β : Fin h → ℝ | ∀ j, |β j| ≤ 1} := by
  ext β
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
