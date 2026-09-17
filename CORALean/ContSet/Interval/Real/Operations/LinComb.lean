import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.linComb`

The smallest box holding both, coordinate by coordinate. Exact for boxes: a
segment between two of them never leaves the enclosing box, so nothing looser
is needed.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.linComb (I₁ I₂ : Interval α) : Interval α where
  inf := ofEntry fun i => min (entry I₁.inf i) (entry I₂.inf i)
  sup := ofEntry fun i => max (entry I₁.sup i) (entry I₂.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
