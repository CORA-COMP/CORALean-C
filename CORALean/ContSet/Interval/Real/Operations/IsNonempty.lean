import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.IsNonempty`

Bounds that do not cross, coordinate by coordinate: CORA's emptiness check,
read the other way round. `Theorems/IsNonempty` gives the equivalence with
`construct.Nonempty` and its negation, which is every use of this predicate.
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

/-- Bounds that do not cross, coordinate by coordinate. -/
def Interval.IsNonempty (I : Interval α) : Prop := ∀ i : ι, entry I.inf i ≤ entry I.sup i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
