import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowAlign

/-!
# Addition is exact

`exactAdd` agrees with ℝ on the nose, once both are aligned to the smaller
exponent by `two_zpow_align`. What
`SoundFloatArithmetic.add_le_addUp`/`addDown_le_add` compose with the
rounding step to get.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_exactAdd (a b : Dyadic p) :
    toReal (exactAdd a b) = toReal a + toReal b := by
  rw [toReal_def, toReal_def, toReal_def, exactAdd]
  push_cast
  rw [add_mul, mul_assoc, mul_assoc, two_zpow_align (min_le_left a.exponent b.exponent),
    two_zpow_align (min_le_right a.exponent b.exponent)]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
