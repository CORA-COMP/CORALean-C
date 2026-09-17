import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection

/-!
# `HPolytope.intersection` is exactly the intersection

`mem_intersection_iff` read as a set equality. Intersection is the operation a halfspace
description is exact under and a vertex description is not, which is why the
tree converts to this representation to intersect.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.intersection_exact (P₁ P₂ : HPolytope α) :
    P₁.construct ∩ P₂.construct = (P₁.intersection P₂).construct :=
  Set.ext fun _ => HPolytope.mem_intersection_iff.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
