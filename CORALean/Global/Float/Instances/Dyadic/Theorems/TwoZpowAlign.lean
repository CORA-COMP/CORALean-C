import CORALean.Global.Float.Instances.Dyadic.Operations

/-!
# Splitting a power of two across an exponent shift

A mantissa scaled by `2 ^ (f - e)` and read at `e` is that number read at `f`.
Shared by `toReal_align` and `toReal_exactAdd`, both of which move a dyadic
from its own exponent onto a common, smaller one.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic


-- =======================================  MAIN THEOREM  ======================================= --

theorem two_zpow_align {e f : ℤ} (h : e ≤ f) :
    (2 : ℝ) ^ (f - e).toNat * 2 ^ e = 2 ^ f := by
  rw [← zpow_natCast (2 : ℝ) (f - e).toNat, Int.toNat_of_nonneg (sub_nonneg.mpr h),
    ← zpow_add₀ (two_ne_zero), sub_add_cancel]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
