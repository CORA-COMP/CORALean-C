import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealAlign

/-!
# Comparison agrees with ℝ

Aligned to the common exponent by `toReal_align`, both numbers are a mantissa
times one positive scale, so comparing them is comparing integers. Shared by
`toReal_minimum`, `toReal_maximum` and `toReal_le_of_le`, each of which needs
both directions or only the one `SoundFloatArithmetic` asks for.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_iff (a b : Dyadic p) : le a b = true ↔ toReal a ≤ toReal b := by
  rw [le, decide_eq_true_eq, toReal_align a (min_le_left a.exponent b.exponent),
    toReal_align b (min_le_right a.exponent b.exponent)]
  exact ⟨fun h => mul_le_mul_of_nonneg_right (Int.cast_le.mpr h) (le_of_lt (zpow_pos two_pos _)),
         fun h => Int.cast_le.mp (le_of_mul_le_mul_right h (zpow_pos two_pos _))⟩

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
