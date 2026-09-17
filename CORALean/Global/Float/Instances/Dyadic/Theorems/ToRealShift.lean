import CORALean.Global.Float.Instances.Dyadic.Operations

/-!
# Reading a dyadic after dropping bits into its exponent

Dropping `k` bits and raising the exponent by `k` leaves only mantissas to
compare. Shared by `roundDown_le` and `le_roundUp`, both of which round by
shifting the mantissa down and reading the result back at the original scale.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Dropping `k` bits and raising the exponent by `k` leaves only mantissas to compare. -/
theorem toReal_shift (m e : ℤ) (k : ℕ) :
    toReal (⟨m, e + k⟩ : Dyadic p) = ((m * 2 ^ k : ℤ) : ℝ) * 2 ^ e := by
  rw [toReal_def, zpow_add₀ (two_ne_zero), zpow_natCast]
  push_cast
  ring

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
