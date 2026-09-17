import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.LinProg.Float.API

/-!
# `Interval.boundNegProj`

A box answers the negated coordinate direction with its own lower bound,
negated, exactly.
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

def Interval.boundNegProj (I : Interval 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 I.construct (-LinearMap.proj j) :=
  ⟨neg (I.inf j), fun x hx => by
    -- ascribed, `linarith` reading membership no further than reducible defeq
    have h : toReal (I.inf j) ≤ x j := (hx j).1
    show -(x j) ≤ toReal (neg (I.inf j))
    rw [toReal_neg]
    linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
