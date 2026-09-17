import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter

/-!
# `Zonotope.reduceGirard` over-approximates the zonotope

Below the order the zonotope is returned untouched, above it the claim is
`reduceBy_outer` at the partition Girard's rule chose.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceGirard_outer (Z : Zonotope 𝕋 n) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
