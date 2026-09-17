import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.point`

Zero width, which is the singleton. Composed with `plus` this is a translation,
so the representation needs no separate one — which is why a bias, a jump reset
and a linearisation offset all reach it through here.

The membership fact is `Theorems/MemPoint.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.point (v : α) : Interval α := ⟨v, v⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
