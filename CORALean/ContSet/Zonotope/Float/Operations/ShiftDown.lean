import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.shiftDown`

The box midpoint added to the centre, rounded down. The exact midpoint need
not be a float — `[5, 6]` gives 5.5 — so the gap between the two roundings is
what `absorbError` leaves behind.
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

/-- The box midpoint added to the centre, rounded each way. The exact midpoint
need not be a float — `[5, 6]` gives 5.5 — so the gap between the two roundings
is what `absorbError` leaves behind. -/
def Zonotope.shiftDown (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addDown (Z.c i) (half (addDown (Z.E.inf i) (Z.E.sup i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
