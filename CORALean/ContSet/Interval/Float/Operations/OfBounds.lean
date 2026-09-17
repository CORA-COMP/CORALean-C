import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.LinProg.Float.API

/-!
# `Interval.ofBounds`, over a floating-point scalar

A box read off `2n` certified float bounds, one per coordinate direction, the
lower ones arriving against `-eⱼ`. Nothing rounds: each bound was already
rounded outward where it was computed, and negating a float is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {S : Set (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.ofBounds (up : ∀ j, FloatBound 𝕋 S (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 S (-LinearMap.proj j)) : Interval 𝕋 n where
  inf := fun j => neg (lo j).val
  sup := fun j => (up j).val

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
