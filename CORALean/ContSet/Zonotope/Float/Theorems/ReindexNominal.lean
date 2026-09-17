import CORALean.ContSet.Zonotope.Float.Operations.Reindex
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# A relabelled zonotope's nominal part is the exact layer's `map` at the relabelling

Definitional: `nominal` transposes the generator matrix and reads it into ℝ,
and both of those commute with moving the coordinate axis.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Definitional: `nominal` transposes the generator matrix and reads it into ℝ,
and both of those commute with moving the coordinate axis. -/
theorem Zonotope.reindex_nominal (e : Fin m ≃ Fin n) (Z : Zonotope 𝕋 n) :
    InflatedContSet.nominal (Z.reindex e)
      = Real.Zonotope.map (reindexLin e) (InflatedContSet.nominal Z) := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
