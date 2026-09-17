import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.plus`

CORA's `@interval/plus`: bounds add.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.plus (I₁ I₂ : Interval α) : Interval α where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
