import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.Interval.Real.Theorems.ReindexExact

/-!
# `Interval.reindex` is exactly the relabelled box, in float too

The only float guarantee in the repository that is an equality rather than an
enclosure, and the reason is that nothing rounds: the nominal box of a
relabelled interval *is* the relabelled nominal box, by `rfl`, so the exact
layer's theorem is the whole proof.
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

theorem Interval.reindex_exact (e : Fin m ≃ Fin n) (I : Interval 𝕋 n) :
    (I.reindex e).construct = reindexLin e '' I.construct :=
  Real.Interval.reindex_exact e I.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
