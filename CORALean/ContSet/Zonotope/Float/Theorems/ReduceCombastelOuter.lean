import CORALean.ContSet.Zonotope.Float.Operations.ReduceCombastel
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter

/-!
# `Zonotope.reduceCombastel` over-approximates the zonotope

Same two cases as Girard's rule, at Combastel's partition instead — the metric
never appears, which is `reduceBy_outer`'s whole point.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Same two cases, at Combastel's partition instead of Girard's — the metric
never appears, which is `reduceBy_outer`'s whole point. -/
theorem Zonotope.reduceCombastel_outer (Z : Zonotope 𝕋 n) (o : ℕ) :
    Z.construct ⊆ (Z.reduceCombastel o).construct := by
  unfold Zonotope.reduceCombastel
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
