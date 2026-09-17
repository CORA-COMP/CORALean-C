import CORALean.ContSet.Interval.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# `Interval.mtimesIntervalMat` over-approximates every matrix in the box

The whole content is one scalar fact, `mul_between_corners`: a product of two
bounded factors is bounded by the four corner products. Applying it entrywise
and summing, `Finset.sum_le_sum` twice, is all that is left to do here.

Outer and never exact for the same reason `Interval.mtimes` is not: the rows are
summed independently, so the result admits combinations of the corner extremes
that no single matrix in the box realises.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- and a sum of such products lies between the two corner sums, term by term
theorem Interval.mtimesIntervalMat_outer (IM : Interval (Mat ℝ m n))
    (I : Interval (Vec ℝ n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' I.construct)
      ⊆ (Interval.mtimesIntervalMat IM I).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hx, rfl⟩ := hy
  intro i
  have hA' := Interval.mem_mat_iff.mp hA
  -- `entry` at a vector is the coordinate, definitionally
  have hx' : ∀ k, I.inf k ≤ x k ∧ x k ≤ I.sup k := fun k => hx k
  show (∑ k, Interval.mulLo (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k))
        ≤ ∑ k, A i k * x k
      ∧ (∑ k, A i k * x k)
        ≤ ∑ k, Interval.mulHi (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)
  exact ⟨Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_corners (hA' i k).1 (hA' i k).2
             (hx' k).1 (hx' k).2).1,
         Finset.sum_le_sum fun k _ =>
           (Interval.mul_between_corners (hA' i k).1 (hA' i k).2
             (hx' k).1 (hx' k).2).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
