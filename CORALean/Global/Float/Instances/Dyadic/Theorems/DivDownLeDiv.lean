import CORALean.Global.Float.Instances.Dyadic.Theorems.MantissaPos
import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDivEq
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMk

/-!
# Division, rounded down, never overshoots

The same fact as `RoundDownLe`, `Int.ediv_mul_le`, applied one step earlier:
the quotient is rounded while it is still two integers, since afterwards it is
a rational nothing on the grid equals. A positive divisor is what the
direction depends on — with a negative one the floor of the mantissa quotient
is an upper bound, not a lower — and `SoundFloatArithmetic` asks for exactly
that. The grid rounding on top of the quotient only moves the bound further
out, which is `roundDown_le` composed on.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}

/-- Integer division truncates toward zero, which for a positive divisor is down. -/
private theorem quotDown_le_div (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal (quotDown a b) ≤ toReal a / toReal b := by -- --- PROOF ---
  have hm : 0 < b.mantissa := mantissa_pos hb
  have hmR : (0 : ℝ) < (b.mantissa : ℝ) := Int.cast_pos.mpr hm
  rw [toReal_div_eq a b (ne_of_gt hmR), quotDown, toReal_mk]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  rw [le_div_iff₀ hmR]
  exact_mod_cast Int.ediv_mul_le (a.mantissa * 2 ^ p) (ne_of_gt hm)


-- =======================================  MAIN THEOREM  ======================================= --

/-- And the grid rounding on top of it only moves the bound further out. -/
theorem divDown_le_div (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal (divDown a b) ≤ toReal a / toReal b :=
  le_trans (roundDown_le _) (quotDown_le_div a b hb)

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
