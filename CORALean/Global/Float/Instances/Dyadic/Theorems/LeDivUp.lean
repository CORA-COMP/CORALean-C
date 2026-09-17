import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.MantissaPos
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDivEq
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMk

/-!
# Division, rounded up, never undershoots

The same fact as `LeRoundUp`, `Int.ediv_mul_le`, applied one step earlier: the
quotient is rounded while it is still two integers, since afterwards it is a
rational nothing on the grid equals. The upward direction is the downward
one, `quotDown_le_div`, at a negated dividend; the grid rounding on top,
`le_roundUp`, only moves the bound further out.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}

/-- The upward direction is the downward one at a negated dividend. -/
private theorem le_quotUp (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (quotUp a b) := by -- --- PROOF ---
  have hm : 0 < b.mantissa := mantissa_pos hb
  have hmR : (0 : ℝ) < (b.mantissa : ℝ) := Int.cast_pos.mpr hm
  rw [toReal_div_eq a b (ne_of_gt hmR), quotUp, toReal_mk]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  rw [div_le_iff₀ hmR]
  have h := Int.ediv_mul_le (-(a.mantissa * 2 ^ p)) (ne_of_gt hm)
  have h' : a.mantissa * 2 ^ p
      ≤ -(-(a.mantissa * 2 ^ p) / b.mantissa) * b.mantissa := by
    rw [neg_mul]
    linarith
  exact_mod_cast h'


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_divUp (a b : Dyadic p) (hb : 0 < toReal b) :
    toReal a / toReal b ≤ toReal (divUp a b) :=
  le_trans (le_quotUp a b hb) (le_roundUp _)

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
