import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# `linComb`'s generator count

The two incoming blocks, plus one fresh generator for the segment.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope 𝕋 n) :
    (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
