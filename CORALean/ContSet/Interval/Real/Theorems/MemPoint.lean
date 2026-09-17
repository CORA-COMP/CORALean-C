import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# The point interval contains its point

Split out from `Operations/Point.lean`, which used to carry both: one
declaration per file (issue #62) does not make an exception for a fact this
short, and the theorem still travels with `point` by import alone, `Point.lean`
importing nothing from here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

-- both bounds are the point itself, so each coordinate is bounded by equality
theorem Interval.mem_point (v : α) : v ∈ (Interval.point v).construct :=
  fun _ => ⟨le_rfl, le_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
