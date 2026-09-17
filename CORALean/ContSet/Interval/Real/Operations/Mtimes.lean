import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.mtimes`

CORA's `@interval/mtimes`: each row takes the lower endpoint of every product
and the upper one, so a negative `M i k` swaps the bounds it multiplies.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mtimes (M : Mat ℝ m n) (I : Interval (Vec ℝ n)) : Interval (Vec ℝ m) where
  inf := fun i => ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
  sup := fun i => ∑ k, max (M i k * I.inf k) (M i k * I.sup k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
