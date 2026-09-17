import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.center`

The midpoint: CORA's `center`, one half of the split an enclosure proof reads
a box's point through — a centre plus a bounded deviation `Interval.radius`
gives, related to it by `Theorems/AbsSubCenterLe`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.center (I : Interval α) : α := (2:ℝ)⁻¹ • (I.inf + I.sup)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
