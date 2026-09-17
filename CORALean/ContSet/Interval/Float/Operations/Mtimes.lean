import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.mtimes`

`minimum`/`maximum` absorb the sign of `M i k` as `min`/`max` do over ℝ, and
each bound rounds away from the interval.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mtimes (M : Mat 𝕋 m n) (I : Interval 𝕋 n) : Interval 𝕋 m where
  inf := fun i => sumDown fun k => minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k))
  sup := fun i => sumUp fun k => maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
