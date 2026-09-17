import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.Interval.Float.Operations.OfBounds

/-!
# Bounding an inflated representation in a direction

The set is a nominal one plus an error box, so a direction sees the sum of what
each reaches — bound the two parts and add them upward. Every float
representation with an ambient error box answers a linear program this way, and
none of them has to say so separately.

The nominal bound is the exact layer's problem, unchanged: the box only pays for
the rounding that put it there.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N 𝕋 n]


-- =====================================  MAIN DEFINITION  ====================================== --

def InflatedContSet.boundOfParts {c : Vec ℝ n →ₗ[ℝ] ℝ} {s : S}
    (u : FloatBound 𝕋 (nominalSet s) c) (v : FloatBound 𝕋 (error s).construct c) :
    FloatBound 𝕋 (InflatedContSet.construct s) c :=
  u.add v

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
