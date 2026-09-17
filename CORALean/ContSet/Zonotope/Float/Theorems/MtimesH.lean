import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `mtimes` does not change the generator count
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.mtimes_h (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    (Zonotope.mtimes M Z).h = Z.h := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
