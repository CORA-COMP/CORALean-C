import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.centerResidual`

Storing the lower of the two directed roundings of a centre sum leaves this
much to pay into the box.
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

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def Zonotope.centerResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
