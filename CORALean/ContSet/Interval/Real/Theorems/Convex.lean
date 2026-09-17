import CORALean.ContSet.Interval.Real.Interval

/-!
# An interval is convex

Each coordinate is bounded independently, so a weighted average of two admissible
points is admissible coordinate by coordinate. Holds for any bounds, the empty
case included.

What an integral valued in the set needs, being a limit of convex combinations.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.convex_construct (I : Interval α) : Convex ℝ I.construct := by -- --- PROOF ---
  intro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  rw [Entrywise.entry_add, Entrywise.entry_smul, Entrywise.entry_smul]
  -- the weights sum to one, so a constant is its own weighted average
  have hinf : a * entry I.inf i + b * entry I.inf i = entry I.inf i := by
    rw [← add_mul, hab, one_mul]
  have hsup : a * entry I.sup i + b * entry I.sup i = entry I.sup i := by
    rw [← add_mul, hab, one_mul]
  constructor
  · linarith [mul_le_mul_of_nonneg_left h1.1 ha, mul_le_mul_of_nonneg_left h2.1 hb]
  · linarith [mul_le_mul_of_nonneg_left h1.2 ha, mul_le_mul_of_nonneg_left h2.2 hb]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
