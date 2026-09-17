import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter

/-!
# Girard's reduction over-approximates

Two cases: below the order there is nothing to do, and above it the rule is a
partition like any other, so `reduceBy_outer` closes it. Girard's metric appears
nowhere — that is the point of stating the enclosure at an arbitrary partition.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceGirard_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
