import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.ErrorRadius
import CORALean.ContSet.Zonotope.Float.Operations.ShiftDown
import CORALean.ContSet.Zonotope.Float.Operations.ShiftUp

/-!
# `Zonotope.absorbError`

Trade the box for `n` generators about its own midpoint. Over ℝ this moves
nothing; here the shifted centre must be stored as a float, so the box is left
holding what that rounding still owes rather than becoming `[0, 0]`.

`shiftDown`, `shiftUp` and `errorRadius` are shared with `reduceAndAbsorbBy`,
which does this and a reduction in one pass.
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

def Zonotope.absorbError (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z.h + n
  c := Z.shiftDown
  G := fun i => Fin.append (Z.G i) (diagonalBlock Z.errorRadius i)
  E := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
