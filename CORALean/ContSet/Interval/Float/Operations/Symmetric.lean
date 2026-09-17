import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.symmetric`

The box `[-r, r]`, which is what a bound known only in magnitude gives.
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

def Interval.symmetric (r : Vec 𝕋 n) : Interval 𝕋 n := ⟨fun i => neg (r i), r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
