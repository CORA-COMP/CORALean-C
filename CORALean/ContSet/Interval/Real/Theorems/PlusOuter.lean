import CORALean.ContSet.Interval.Real.Operations.Plus

/-!
# `Interval.plus` encloses the Minkowski sum

Coordinatewise, and with no nonemptiness hypothesis, which is what separates it
from the exactness claim: `[1, 0] + [0, 10]` is `∅` as a set but `[1, 10]` by
the definition, so the inclusion survives crossed bounds and the equality does
not. The float layer refines this one for that reason.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.plus_outer (I₁ I₂ : Interval α) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct := by
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ i
  rw [Interval.plus, Entrywise.entry_add, Entrywise.entry_add, Entrywise.entry_add]
  exact ⟨add_le_add (hx₁ i).1 (hx₂ i).1, add_le_add (hx₁ i).2 (hx₂ i).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
