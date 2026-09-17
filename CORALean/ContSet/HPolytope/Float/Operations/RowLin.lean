import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `rowLin`, over a floating-point scalar

Row `i` of a float matrix, as the functional over ℝ that it denotes. Every
bound in this layer is stated against one of these.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` of a float matrix, as the functional over ℝ that it denotes. Every
bound below is stated against one of these. -/
abbrev rowLin (M : Mat 𝕋 q n) (i : Fin q) : Vec ℝ n →ₗ[ℝ] ℝ :=
  Real.HPolytope.rowLin (toRealMat M) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
