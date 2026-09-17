import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MulLo

/-!
# Intervals: multiplication by an interval matrix

CORA writes this as `mtimes` too, dispatching on the argument. A product of two
scalar intervals reaches exactly the four corner products' hull, so a row is the
sum of those hulls — and that sum is the only widening, coordinates of the
argument being allowed to vary independently of one another.

Unlike `Zonotope.mtimesIntervalMat` no fresh generator is spent: a box has
nowhere to put one, and the corner bounds are already the tightest a box can
state per row.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mtimesIntervalMat (IM : Interval (Mat ℝ m n)) (I : Interval (Vec ℝ n)) :
    Interval (Vec ℝ m) where
  inf := fun i => ∑ k, Interval.mulLo (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)
  sup := fun i => ∑ k, Interval.mulHi (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
