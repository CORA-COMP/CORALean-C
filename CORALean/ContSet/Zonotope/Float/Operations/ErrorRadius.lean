import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.errorRadius`

The box radius, rounded up; halving is exact, so only the difference rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box radius, rounded up; halving is exact, so only the difference rounds. -/
def Zonotope.errorRadius (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => half (subUp (Z.E.sup i) (Z.E.inf i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
