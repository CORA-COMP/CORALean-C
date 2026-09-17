import CORALean.ContSet.HPolytope.Real.Operations.Intersection
import CORALean.ContSet.HPolytope.Real.Operations.Ineqs

/-!
# `HPolytope.slab`

`Ae x ∈ [lo, hi]`: an equality row with room in it. One row per constraint, as an
equality has, but with a right-hand side that can be widened.

This is what a float layer needs. An inequality absorbs its rounding by raising
`b`; an equality has no slack of its own, since any rounding of `Ae` or `be`
names a different hyperplane and a hyperplane has empty interior. Widening the
right-hand side into an interval is where that rounding can go.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.slab (Ae : Mat ℝ q n) (lo hi : Vec ℝ q) : HPolytope (Vec ℝ n) :=
  (HPolytope.ineqs Ae hi).intersection (HPolytope.ineqs (-Ae) (-lo))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
