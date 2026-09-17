import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.Interval.Real.Operations.Reindex

/-!
# A relabelled box's nominal part is the relabelled nominal box

Nothing rounds, so this is `rfl`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.reindex_nominal (e : Fin m ≃ Fin n) (I : Interval 𝕋 n) :
    (I.reindex e).nominal = I.nominal.reindex e := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
