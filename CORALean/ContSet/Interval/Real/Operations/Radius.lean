import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.radius`

Half the width: CORA's `rad`, the other half of the centre-deviation split
`Interval.center` gives a box's point. `Theorems/AbsSubCenterLe` is the bound
relating the two.
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

noncomputable def Interval.radius (I : Interval α) : α := (2:ℝ)⁻¹ • (I.sup - I.inf)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
