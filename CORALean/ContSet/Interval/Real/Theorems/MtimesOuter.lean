import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints

/-!
# `Interval.mtimes` over-approximates the image under a linear map

Each summand `M i k * x k` lies between the two endpoint products;
`mul_between_endpoints` is where `min`/`max` absorb the sign of `M i k`,
leaving one case split. Summing over `k` finishes it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mtimes_outer (M : Mat ℝ m n) (I : Interval (Vec ℝ n)) :
    (M *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  -- `entry` at a vector is the coordinate, definitionally
  have hxk : ∀ k, I.inf k ≤ x k ∧ x k ≤ I.sup k := fun k => hx k
  show (∑ k, min (M i k * I.inf k) (M i k * I.sup k)) ≤ ∑ k, M i k * x k
      ∧ (∑ k, M i k * x k) ≤ ∑ k, max (M i k * I.inf k) (M i k * I.sup k)
  exact ⟨Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_endpoints (hxk k).1 (hxk k).2).1,
         Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_endpoints (hxk k).1 (hxk k).2).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
