import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# `Zonotope.radiusReach`

What an interval matrix's radius can add to a coordinate, over every matrix the
interval denotes: the radius weighted by the zonotope's own reach in each
column.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the radius can add to coordinate `i`, over every matrix denoted. -/
noncomputable def Zonotope.radiusReach (IM : Interval (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n))
    (i : Fin m) : ℝ :=
  ∑ j, IM.radius i j * Z.absBound j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
