import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.intersection`, over a floating-point scalar

Coordinatewise and exactly. Nothing rounds: choosing the larger of two stored
lower bounds, or the smaller of two upper ones, returns one of them.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.intersection (I₁ I₂ : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun j => maximum (I₁.inf j) (I₂.inf j)
  sup := fun j => minimum (I₁.sup j) (I₂.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
