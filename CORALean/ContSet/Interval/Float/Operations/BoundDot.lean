import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.LinProg.Float.API

/-!
# `Interval.boundDot`

A box answers an arbitrary direction too: a linear function of one coordinate
is largest at one end of its range, so each term takes the endpoint its sign
picks and the terms are summed upward.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box answers an arbitrary direction too: a linear function of one
coordinate is largest at one end of its range, so each term takes the endpoint
its sign picks and the terms are summed upward. -/
def Interval.boundDot (I : Interval 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 I.construct c where
  val := sumUp fun j => maximum (mulUp (a j) (I.sup j)) (mulUp (a j) (I.inf j))
  le x hx := by
    rw [hc x]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    have hlo : toReal (I.inf j) ≤ x j := (hx j).1
    have hhi : x j ≤ toReal (I.sup j) := (hx j).2
    rw [toReal_maximum]
    rcases le_total 0 (toReal (a j)) with hs | hs
    · refine le_trans ?_ (le_max_left _ _)
      exact le_trans (mul_le_mul_of_nonneg_left hhi hs) (mul_le_mulUp _ _)
    · refine le_trans ?_ (le_max_right _ _)
      exact le_trans (mul_le_mul_of_nonpos_left hlo hs) (mul_le_mulUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
