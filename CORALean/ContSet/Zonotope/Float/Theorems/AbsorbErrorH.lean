import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

/-!
# `absorbError` spends the box as `n` fresh generators
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.absorbError_h (Z : Zonotope 𝕋 n) : Z.absorbError.h = Z.h + n := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
