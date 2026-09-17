import CORALean.Global.Float.Instances.Dyadic.Operations

/-!
# A positive dyadic has a positive mantissa

The scale is positive, so the sign is the mantissa's. Both `quotDown_le_div`
and `le_quotUp` need the divisor's mantissa positive, to divide by it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mantissa_pos {b : Dyadic p} (hb : 0 < toReal b) : 0 < b.mantissa := by -- --- PROOF ---
  rw [toReal_def] at hb
  by_contra h
  have hc : ((b.mantissa : ℝ)) ≤ 0 := Int.cast_nonpos.mpr (not_lt.mp h)
  have hz := mul_le_mul_of_nonneg_right hc (le_of_lt (zpow_pos two_pos b.exponent))
  rw [zero_mul] at hz
  exact absurd hb (not_lt.mpr hz)

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
