import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.plus`

Each bound rounds away from the interval: `inf` down, `sup` up.
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

def Interval.plus (I₁ I₂ : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i => addDown (I₁.inf i) (I₂.inf i)
  sup := fun i => addUp (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
