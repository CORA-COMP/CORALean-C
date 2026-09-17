import CORALean.ContSet.Interval.Real.Theorems.IsBounded
import CORALean.ContSet.Interval.Real.Theorems.IsClosed

/-!
# An interval is compact

`CompactSet` asks for compactness as a single field, so the two halves are
combined here rather than re-exported. `Vec ℝ n` is a proper space, where
Heine–Borel makes closed and bounded exactly compact.

At `Vec ℝ n`, since boundedness is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isCompact_construct (I : Interval (Vec ℝ n)) : IsCompact I.construct :=
  Metric.isCompact_of_isClosed_isBounded I.isClosed_construct I.isBounded_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
