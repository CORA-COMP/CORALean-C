import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Real.Operations.Slab
import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact

/-!
# Membership in `HPolytope.slab`
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_slab_iff {Ae : Mat ℝ q n} {lo hi : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.slab Ae lo hi).construct ↔
      ∀ i, lo i ≤ (Ae *ᵥ x) i ∧ (Ae *ᵥ x) i ≤ hi i := by -- --- PROOF ---
  have hand : x ∈ (HPolytope.slab Ae lo hi).construct ↔
      x ∈ (HPolytope.ineqs Ae hi).construct
        ∧ x ∈ (HPolytope.ineqs (-Ae) (-lo)).construct := HPolytope.mem_intersection_iff
  rw [hand, HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
  -- both directions, the lower bound being the negated row read back
  constructor
  · rintro ⟨hhi, hlo⟩ i
    have h := hlo i
    rw [Matrix.neg_mulVec, Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff] at h
    exact ⟨h, hhi i⟩
  · intro h
    refine ⟨fun i => (h i).2, fun i => ?_⟩
    rw [Matrix.neg_mulVec, Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff]
    exact (h i).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
