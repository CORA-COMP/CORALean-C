import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MulLo
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints

/-!
# A product of two bounded factors stays between the four corner products

`mulLo`/`mulHi` are the least/greatest of `a * c`, `a * d`, `b * c`, `b * d`.
This is the scalar fact every interval-matrix product in the tree reduces to:
apply `mul_between_endpoints` once holding the argument fixed and moving the
coefficient, once the other way, no case split on signs needed. Was file-local
to `MtimesIntervalMatOuter`; `matMul_outer` needs it too, hence public here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A product of two bounded factors never leaves the hull of the four corner
products. -/
theorem Interval.mul_between_corners {a b c d y x : ℝ} (hy₁ : a ≤ y) (hy₂ : y ≤ b)
    (hx₁ : c ≤ x) (hx₂ : x ≤ d) :
    Interval.mulLo a b c d ≤ y * x ∧ y * x ≤ Interval.mulHi a b c d := by -- --- PROOF ---
  have hy := Interval.mul_between_endpoints (c := x) hy₁ hy₂
  have ha := Interval.mul_between_endpoints (c := a) hx₁ hx₂
  have hb := Interval.mul_between_endpoints (c := b) hx₁ hx₂
  constructor
  · calc Interval.mulLo a b c d
        ≤ min (a * x) (b * x) := min_le_min ha.1 hb.1
      _ = min (x * a) (x * b) := by rw [mul_comm a x, mul_comm b x]
      _ ≤ x * y                := hy.1
      _ = y * x                := mul_comm x y
  · calc y * x = x * y := mul_comm y x
      _ ≤ max (x * a) (x * b) := hy.2
      _ = max (a * x) (b * x) := by rw [mul_comm x a, mul_comm x b]
      _ ≤ Interval.mulHi a b c d := max_le_max ha.2 hb.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
