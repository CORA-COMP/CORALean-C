import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.HPolytope.Float.Operations.MemIneqsIff

/-!
# `HPolytope.ofBounds` encloses, over a floating-point scalar

The rounding has already been paid where each bound was combined, and nothing
rounds here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ} {S : Set (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.subset_ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S (rowLin Aq i)) :
    S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun x hx => HPolytope.mem_ineqs_iff.mpr fun i => (u i).le x hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
