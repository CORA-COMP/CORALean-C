import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.absBound`

How far a coordinate of a zonotope can reach from the origin: the interval
hull's bound, read off without building the hull.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far coordinate `j` can reach from the origin. -/
def Zonotope.absBound (Z : Zonotope (Vec ℝ n)) (j : Fin n) : ℝ :=
  |Z.c j| + ∑ l, |Z.G l j|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
