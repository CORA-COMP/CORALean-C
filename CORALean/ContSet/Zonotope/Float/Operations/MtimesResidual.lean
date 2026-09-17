import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError

/-!
# `Zonotope.mtimesResidual`

What `mtimes` owes beyond its nominal part: the centre, rounded, and the
generators, each entry known only to within `matMulDiff`'s rounding gap.
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

/-- What `mtimes` owes beyond its nominal part: the centre, and the generators. -/
def Zonotope.mtimesResidual (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Interval 𝕋 m :=
  (Interval.residual (mulVecDown M Z.c) (mulVecUp M Z.c) (mulVecDown M Z.c)).plus
    (Zonotope.generatorError (matMulDiff M Z.G))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
