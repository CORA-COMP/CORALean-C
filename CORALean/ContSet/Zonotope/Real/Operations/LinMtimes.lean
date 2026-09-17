import CORALean.ContSet.Zonotope.Real.Operations.Map

/-!
# Zonotopes: multiplication by a single linear map

`map` at the one map a plain matrix denotes. An operation of its own rather than
a use of `map` because a caller holds *matrix data*, which is what an algorithm
can compute with, and `LinMapSet` is what turns that into a map.

At `Vec` this is `mtimes`; at `Mat` it is matrix multiplication of a matrix
zonotope, from either side.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `map` at a map read off `M`, which is sound whenever `M` denotes that one
map and no other. Its guarantee is `lmtimes_singleton_outer`. -/
def Zonotope.mapOf (f : α →ₗ[ℝ] β) (Z : Zonotope α) : Zonotope β := Z.map f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
