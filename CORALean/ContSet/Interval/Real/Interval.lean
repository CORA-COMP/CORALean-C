import CORALean.Global.Entrywise

/-!
# Intervals: the representation

CORA's `interval`, with the same `inf` and `sup` fields, denoting the points
each coordinate's bounds admit.

Over any ambient type that has coordinates, so `Interval (Mat ℝ m n)` is CORA's
`intervalMatrix` and needs no separate representation: only which index set the
bounds run over changes.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- ========================================  MAIN TYPE  ========================================= --

structure Interval (α : Type) where
  inf : α
  sup : α

/-- `sup i < inf i` denotes the empty set `∅` -/
def Interval.construct (I : Interval α) : Set α :=
  {x | ∀ i, entry I.inf i ≤ entry x i ∧ entry x i ≤ entry I.sup i}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
