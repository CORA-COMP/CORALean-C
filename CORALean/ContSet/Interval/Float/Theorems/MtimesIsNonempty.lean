import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.IsNonempty

/-!
# A rounded image box still has its bounds in order

The counterpart of the exact statement, and it needs the rounding directions to
say it: the lower bound rounds down and the upper one rounds up, so the gap the
exact `min ≤ max` leaves only widens.

Stated of `nominal`, which is the interval this one denotes and the only one a
layer's committed centre is measured in — `Layer.linearWithError` over floats
asks for exactly this of the box a neuron merge computes.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mtimes_isNonempty (M : Mat 𝕋 m n) (I : Interval 𝕋 n) :
    (Interval.mtimes M I).nominal.IsNonempty := fun i => by
  -- one term of the row: the down-rounded product at `inf` sits between the two
  have hle : ∀ k, toReal (minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k)))
      ≤ toReal (maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))) := by -- --- PROOF ---
    intro k
    rw [toReal_minimum, toReal_maximum]
    exact le_trans (min_le_left _ _) (le_trans (le_trans (mulDown_le_mul _ _)
      (mul_le_mulUp _ _)) (le_max_left _ _))
  exact le_trans (sumDown_le_sum _)
    (le_trans (Finset.sum_le_sum fun k _ => hle k) (sum_le_sumUp _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
