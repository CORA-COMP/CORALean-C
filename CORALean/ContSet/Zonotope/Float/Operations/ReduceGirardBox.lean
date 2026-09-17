import CORALean.ContSet.Zonotope.Float.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Float.Operations.ReduceByBox
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# `Zonotope.reduceGirardBox`

The error `reduceGirard` pays, as `Real`'s own `reduceBox`: `reduceByBox` at
the partition `girardSplit` picks, and the origin where the order is already
met and nothing is dropped. So `reduceGirard Z o` reaches no further than `Z`
plus this, which is the reverse of `reduceGirard_outer`.

Not a `Reduce` operation and no class instantiates it: `Reduce` obliges the
outer direction only, while a box for the reverse one is a fact about the
particular rule `reduce` runs.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `reduceGirard` absorbs the dropped generators into, on its own —
and the origin at an order already met, where nothing is dropped. -/
noncomputable def Zonotope.reduceGirardBox (Z : Zonotope 𝕋 n) (o : ℕ) : Real.Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then Z.reduceByBox (Z.girardSplit o hlt) else Real.Zonotope.ofPoint 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
