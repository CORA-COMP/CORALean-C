import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.LinProg.Float.API

/-!
# `Interval.boundProj`

A box answers a coordinate direction with its own bound, exactly. Every
representation carrying an ambient error box charges its rounding through
these.
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

/-- A box answers a coordinate direction with its own bound, exactly. Every
representation carrying an ambient error box charges its rounding through
these. -/
def Interval.boundProj (I : Interval 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 I.construct (LinearMap.proj j) :=
  ⟨I.sup j, fun _ hx => (hx j).2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
