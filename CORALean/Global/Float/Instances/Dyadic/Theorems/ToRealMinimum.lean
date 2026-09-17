import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff

/-!
# `minimum` is exact

`le_iff` picks the smaller side directly, which is what lets `minimum` absorb
a sign without widening anything. What `SoundFloatArithmetic.toReal_minimum`
needs from `Dyadic`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_minimum (a b : Dyadic p) :
    toReal (minimum a b) = min (toReal a) (toReal b) := by
  by_cases h : le a b = true
  · rw [minimum, if_pos h, min_eq_left ((le_iff a b).mp h)]
  · rw [minimum, if_neg h, min_eq_right (not_le.mp (h ∘ (le_iff a b).mpr)).le]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
