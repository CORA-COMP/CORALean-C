import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Real.Operations.MemSlabIff

/-!
# Membership in a float halfspace description, in the stored fields

What this polytope denotes is the exact layer's `ineqs` intersected with its
`slab`, so membership arrives as a nesting of three lemmas. This unfolds it once
into the two blocks the stored matrices state: a bound per inequality row, and
an interval per equality row.

It is the form every operation and every conversion at this layer states its
obligation in, which is why `Operations/` here reaches back into `Theorems/`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_construct_iff [SoundFloatArithmetic 𝕋] {P : HPolytope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ P.construct ↔
      (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i))
        ∧ ∀ i, toReal (P.be.inf i) ≤ (toRealMat P.Ae *ᵥ x) i
               ∧ (toRealMat P.Ae *ᵥ x) i ≤ toReal (P.be.sup i) := by -- --- PROOF ---
  have hand : x ∈ P.construct ↔
      x ∈ (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b)).construct
        ∧ x ∈ (Real.HPolytope.slab (toRealMat P.Ae) (toRealVec P.be.inf)
            (toRealVec P.be.sup)).construct := Real.HPolytope.mem_intersection_iff
  rw [hand, Real.HPolytope.mem_ineqs_iff, Real.HPolytope.mem_slab_iff]
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
