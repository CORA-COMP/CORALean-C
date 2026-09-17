import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.residual`

The box an operation owes when it stores a rounded vector: the intended value
lies in `[lo, hi]` but `stored` was written down, so `[lo - stored, hi - stored]`
covers the difference.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.residual (lo hi stored : Vec 𝕋 n) : Interval 𝕋 n :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
