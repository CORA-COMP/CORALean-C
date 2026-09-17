import CORALean.ContSet.ContSet.ContSet

/-!
# Representations that denote a compact set

One field rather than two: an algorithm enclosing an integral needs the set
closed *and* bounded, and over a normed space compactness is exactly both, so
`isClosed_construct` and `isBounded_construct` are theorems here instead of
obligations a representation has to discharge twice.

Compactness rather than the pair also picks the right instances: a merely closed
and bounded representation is one whose affine images need not be closed, and
those are the sets `inputSolution` is built from.

Over a normed space, which is where `IsCompact.isClosed` and
`IsCompact.isBounded` both apply and where every representation instantiating
this already states its lemmas.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [ContSet S α]


-- ========================================  MAIN TYPE  ========================================= --

/-- Everything this representation denotes is compact. -/
class CompactSet (S : Type) (α : outParam Type) [NormedAddCommGroup α] [NormedSpace ℝ α]
    [ContSet S α] where
  isCompact_construct (s : S) : IsCompact (construct s)

theorem CompactSet.isClosed_construct [CompactSet S α] (s : S) : IsClosed (construct s) :=
  (CompactSet.isCompact_construct s).isClosed

theorem CompactSet.isBounded_construct [CompactSet S α] (s : S) :
    Bornology.IsBounded (construct s) :=
  (CompactSet.isCompact_construct s).isBounded

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
