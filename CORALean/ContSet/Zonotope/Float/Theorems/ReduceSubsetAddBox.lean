import CORALean.ContSet.Zonotope.Float.Operations.Reduce
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceBySubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem

/-!
# `reduce` reaches no further than its operand plus `reduceGirardBox`

The reverse of `reduce_outer`, and `Real`'s own `reduce_subset_add_box`
argument, unchanged: Girard's rule is the whole of the choice, so
`reduceBy_subset_add_box` at the partition it picks closes the case something
is dropped, and the origin closes the case nothing is.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reduce` reaches no further than `Z.construct` widened by
`reduceGirardBox` — the reverse of `reduce_outer`, and what a float run's own
accumulated error needs. -/
theorem Zonotope.reduce_subset_add_box (Z : Zonotope 𝕋 n) (o : ℕ) :
    (Z.reduce o).construct ⊆
      Z.construct + (Zonotope.reduceGirardBox Z o).construct := by -- --- PROOF ---
  unfold Zonotope.reduce Zonotope.reduceGirard Zonotope.reduceGirardBox
  split_ifs with hlt
  · exact Z.reduceBy_subset_add_box _
  · intro x hx
    have h := Set.add_mem_add hx (Real.Zonotope.mem_ofPoint (0 : Vec ℝ n))
    rwa [add_zero] at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
