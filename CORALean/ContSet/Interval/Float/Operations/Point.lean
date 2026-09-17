import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.point`, over a floating-point scalar

Zero width, which is the singleton the stored floats denote. Nothing is
rounded: the point is whatever `𝕋` already holds. The membership fact,
`mem_point`, is `Theorems/MemPoint.lean`.

Composed with `plus` this is a translation, so a layer needs no operation of its
own for a bias — which is how a linear layer's offset reaches a set here.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.point (v : Vec 𝕋 n) : Interval 𝕋 n := ⟨v, v⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
