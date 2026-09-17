import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# The stored midpoint of two centres

Split out of `LinComb.lean` (issue #62): used again by `ConZonotope.linComb`
and by `MidpointMemResidual.lean`, both outside this file.

Rounds the lower of the two directed midpoints; `midpointResidual` is what that
leaves to pay.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stored midpoint of the two centres. -/
def Zonotope.midpoint (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (addDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
