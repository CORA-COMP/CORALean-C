import CORALean.ContSet.ContSet.ContSet

/-!
# Representations that denote a convex set

A property, not an operation: nothing is computed, so unlike `Plus` or `LinComb`
the class has no data field and instantiating it costs a representation only the
proof it already has.

Separate from `CompactSet` for the same reason the operation classes are
separate from each other — the two are independent. An `HPolytope` is convex and
not compact, and a polynomial zonotope would be compact and not convex, so a
class demanding both would shut each of them out of the half it can supply.

Only over a module: convexity needs the scaling and nothing topological. Stated
over what a representation *denotes*, so an algorithm asking for it says exactly
what it needs of the set rather than of the representation.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- Everything this representation denotes is convex. What an integral valued in
the set needs, and what makes `linComb` a convex hull. -/
class ConvexSet (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  convex_construct (s : S) : Convex ℝ (construct s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
