import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Weakening both parts at once

The degenerate case of `map_subset`, for an operation that is already an
inclusion rather than an image: nominal part into nominal part, box into box,
with nothing moving between them.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S T N M : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [ContSet M (Vec ℝ n)]
variable [InflatedContSet S N 𝕋 n] [InflatedContSet T M 𝕋 n]


-- =======================================  MAIN THEOREM  ======================================= --

theorem mono_subset {s : S} {t : T} (hnominal : nominalSet s ⊆ nominalSet t)
    (herror : (error s).construct ⊆ (error t).construct) :
    construct s ⊆ construct t :=
  Set.add_subset_add hnominal herror

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
