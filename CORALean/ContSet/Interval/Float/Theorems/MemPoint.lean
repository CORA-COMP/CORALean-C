import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# The point interval contains its point, over a floating-point scalar

Split out from `Operations/Point.lean`, which used to carry both: one
declaration per file (issue #62) does not make an exception for a fact this
short. Nothing is rounded here; `mem_point` just reads the stored point back
through `toRealVec`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- both bounds are the stored vector, so each coordinate is bounded by equality
theorem Interval.mem_point [SoundFloatArithmetic 𝕋] (v : Vec 𝕋 n) :
    toRealVec v ∈ (Interval.point v).construct := fun _ => ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
