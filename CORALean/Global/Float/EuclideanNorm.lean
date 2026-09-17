import CORALean.Global.EuclideanNorm
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# A Euclidean norm bounded from above, with no square root

`FloatOps` has no square root, and an ellipsoid's support function is
`⟨d, q⟩ + ‖Gᵀd‖₂`, so this is where the float layer meets one — and it needs no
new scalar operation.

An upper bound on `√x` is any `s` with `x ≤ s²`, and `s²` is a multiplication,
which the scalar has in both rounding directions. So what the layer needs is not
a square root but a *check*: an unverified routine proposes `s`, `sqSumUp` bounds
the squared length upward, `mulDown s s` bounds `s²` downward, and the inequality
between them is the proof. That is `LinProg`'s certificate pattern at a scalar —
a wrong candidate yields no bound rather than a wrong one.

The sign of the candidate is never examined. `absolute` is exact, so the bound
is `|s|`, and a routine that returned the negative root still certifies.

Nothing here is specific to an ellipsoid; it is what the layer can say about
`‖·‖₂` at all, which is why it sits in `Global`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}

/-- The squared length of a vector known only in magnitude, rounded up. -/
def sqSumUp (m : Vec 𝕋 k) : 𝕋 := sumUp fun j => mulUp (m j) (m j)

theorem sq_sum_le_sqSumUp {v : Vec ℝ k} {m : Vec 𝕋 k} (hm : ∀ j, |v j| ≤ toReal (m j)) :
    ∑ j, v j ^ 2 ≤ toReal (sqSumUp m) := by -- --- PROOF ---
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  have h0 : (0:ℝ) ≤ toReal (m j) := le_trans (abs_nonneg _) (hm j)
  calc v j ^ 2 = |v j| * |v j| := by rw [← sq_abs, pow_two]
    _ ≤ toReal (m j) * toReal (m j) := mul_le_mul (hm j) (hm j) (abs_nonneg _) h0
    _ ≤ toReal (mulUp (m j) (m j)) := mul_le_mulUp _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- The certificate. `s` is a proposed length: it is a bound exactly when its
square, rounded *down*, still covers the squared length rounded up — one
multiplication in each direction, and no root anywhere. -/
theorem norm₂_le_of_sq_le {v : Vec ℝ k} {m : Vec 𝕋 k} {s : 𝕋}
    (hm : ∀ j, |v j| ≤ toReal (m j))
    (hs : toReal (sqSumUp m) ≤ toReal (mulDown s s)) :
    ‖v‖₂ ≤ toReal (absolute s) := by -- --- PROOF ---
  have hsq : ∑ j, v j ^ 2 ≤ toReal s ^ 2 := by
    have h₁ := sq_sum_le_sqSumUp hm
    have h₂ := mulDown_le_mul s s
    rw [pow_two]
    linarith
  calc ‖v‖₂ = Real.sqrt (∑ j, v j ^ 2) := rfl
    _ ≤ Real.sqrt (toReal s ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |toReal s| := Real.sqrt_sq_eq_abs _
    _ = toReal (absolute s) := (toReal_absolute s).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
