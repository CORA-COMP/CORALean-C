import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.mulLo`

The least of the four corner products of two scalar intervals.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least of the four corner products of `[a, b]` and `[c, d]`. -/
def Interval.mulLo (a b c d : ℝ) : ℝ := min (min (a * c) (a * d)) (min (b * c) (b * d))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
