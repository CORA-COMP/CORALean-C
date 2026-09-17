import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealShift

/-!
# Rounding down never overshoots

`Int.ediv_mul_le`: floor division never overshoots. `roundDown` is exactly that
fact read back through `toReal_shift`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem roundDown_le (d : Dyadic p) : toReal (roundDown d) ≤ toReal d := by
  rw [roundDown, toReal_shift, toReal_def]
  exact mul_le_mul_of_nonneg_right
    (Int.cast_le.mpr (Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)))
    (le_of_lt (zpow_pos two_pos _))

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
