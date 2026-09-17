import CORALean.Global.Float.Instances.Dyadic.Operations

/-!
# The real quotient, read as an integer quotient at a shifted scale

The dividend's `p`-bit shift and the exponent's `-p` cancel, which is what
leaves an integer quotient facing a real one — the whole content of division
going the way it says, shared by `quotDown_le_div` and `le_quotUp`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_div_eq (a b : Dyadic p) (hb : (b.mantissa : ℝ) ≠ 0) :
    toReal a / toReal b
      = ((a.mantissa * 2 ^ p : ℤ) : ℝ) / ((b.mantissa : ℤ) : ℝ)
          * 2 ^ (a.exponent - b.exponent - (p : ℤ)) := by -- --- PROOF ---
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hea : ((2 : ℝ) ^ a.exponent) ≠ 0 := zpow_ne_zero _ h2
  have heb : ((2 : ℝ) ^ b.exponent) ≠ 0 := zpow_ne_zero _ h2
  have hpp : ((2 : ℝ) ^ p) ≠ 0 := pow_ne_zero _ h2
  rw [toReal_def, toReal_def, zpow_sub₀ h2, zpow_sub₀ h2, zpow_natCast]
  push_cast
  field_simp

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
