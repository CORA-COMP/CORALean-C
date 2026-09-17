import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq
import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine

/-!
# A zonotope is compact

Compactness is what carries an integral, and not for the reason an interval is
closed: an affine image of a merely closed set need not be closed, so
compactness does the work. The coefficient cube is the closed unit ball in the
supremum norm, compact because the coefficient space is finite-dimensional, and
the map onto the zonotope is continuous.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- a zonotope is a continuous image of that ball, so compactness carries over
theorem Zonotope.isCompact_construct (Z : Zonotope α) : IsCompact Z.construct := by -- --- PROOF ---
  have himg : Z.construct
      = (fun β : Fin Z.h → ℝ => Z.c + ∑ j, β j • Z.G j) '' Metric.closedBall 0 1 := by
    rw [Zonotope.closedBall_eq]
    ext x
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨β, hβ, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨β, hβ, rfl⟩
  rw [himg]
  exact (isCompact_closedBall 0 1).image Z.continuous_affine

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
