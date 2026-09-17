import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.mulHi`

The greatest of the four corner products of two scalar intervals.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The greatest of the four. -/
def Interval.mulHi (a b c d : ℝ) : ℝ := max (max (a * c) (a * d)) (max (b * c) (b * d))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
