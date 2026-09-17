import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.MtimesResidual

/-!
# `Zonotope.mtimes`

The generator count is untouched, the rounding being paid into the box; the old
box travels through the map as a box, by `Interval.mtimes`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.mtimes (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m where
  h := Z.h
  c := mulVecDown M Z.c
  G := matMulDown M Z.G
  E := (Interval.mtimes M Z.E).plus (Zonotope.mtimesResidual M Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
