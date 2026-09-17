import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy

/-!
# `reduceBy`'s generator count is the kept block plus the box
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.reduceBy_h (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : (Z.reduceBy part).h = q + n := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
