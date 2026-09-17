import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# A one-element set of maps applied to a zonotope

What `LinMtimes` asks of `mapOf`: the union over a singleton is the one map's
image, and that image is exact, so the enclosure holds with nothing to spare.
Stated as an inclusion because that is the shape the interface field has.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `LinMtimes` asks of `mapOf`: a set holding one map is that map. -/
theorem Zonotope.lmtimes_singleton_outer (f : α →ₗ[ℝ] β) (Z : Zonotope α) :
    (⋃ g ∈ ({f} : Set (α →ₗ[ℝ] β)), g '' Z.construct) ⊆ (Zonotope.mapOf f Z).construct := by
  refine Set.iUnion₂_subset fun g hg => ?_
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact (Zonotope.map_exact f Z).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
