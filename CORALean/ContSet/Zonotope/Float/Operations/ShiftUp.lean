import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.shiftUp`

The box midpoint added to the centre, rounded up — the other side of the gap
`shiftDown` leaves for `absorbError` to store.
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

def Zonotope.shiftUp (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
