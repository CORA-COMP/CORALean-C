import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Interval.Real.Theorems.IsCompact

/-!
# A float zonotope is compact

A Minkowski sum of two compact sets, `IsCompact.add`: the nominal zonotope,
compact as a continuous image of the coefficient cube, and the error box,
compact by Heine–Borel. Compactness is what has to be carried rather than
closedness: a sum of two merely closed sets need not be closed, so `IsClosed`
is read off this and not the other way round.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isCompact_construct (Z : Zonotope 𝕋 n) : IsCompact Z.construct :=
  IsCompact.add (nominal Z).isCompact_construct Z.E.nominal.isCompact_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
