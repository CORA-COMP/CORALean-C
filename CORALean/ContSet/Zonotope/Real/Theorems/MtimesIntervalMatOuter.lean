import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

/-!
# Multiplying by an interval matrix over-approximates every matrix in it

The result is [1, Thm. 3.3].

Outer and never exact: the boxed generators are one per coordinate, so what the
radius does to different coordinates is allowed to vary independently, which the
matrices denoted do not.

The centre part is `mtimes` exactly; the whole content is that the leftover
`(A - centre) x` fits inside the diagonal block, which it does because a
coordinate of a zonotope never exceeds `absBound`.

Nonnegativity of the radius is read off the witness rather than assumed: an
`IntervalMat` with crossed bounds denotes nothing, and then there is nothing to
prove.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_mtimesIntervalMat {IM : Interval (Mat ℝ m n)} {Z : Zonotope (Vec ℝ n)}
    (f : Fin (Z.h + m) → ℝ) :
    ∑ j : Fin (Zonotope.mtimesIntervalMat IM Z).h, f j
      = ∑ j, f (Fin.castAdd m j) + ∑ j, f (Fin.natAdd Z.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

-- the image sits in the centre's zonotope widened by what the radius can reach
theorem Zonotope.mtimesIntervalMat_outer (IM : Interval (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' Z.construct)
      ⊆ (Zonotope.mtimesIntervalMat IM Z).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_construct_iff.mp hxmem
  have hrad : ∀ i j, 0 ≤ IM.radius i j :=
    fun i j => (abs_nonneg _).trans (IM.abs_sub_center_le hA (i, j))
  have hxb := Zonotope.abs_le_absBound hβ hx
  -- what the radius is allowed to add to coordinate `i`
  set err : Fin m → ℝ := fun i => ∑ j, (A i j - IM.center i j) * x j with herr
  have herrb : ∀ i, |err i| ≤ Zonotope.radiusReach IM Z i := by
    intro i
    calc |err i|
        ≤ ∑ j, |(A i j - IM.center i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j - IM.center i j| * |x j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, IM.radius i j * Z.absBound j := Finset.sum_le_sum fun j _ =>
          mul_le_mul (IM.abs_sub_center_le hA (i, j)) (hxb j) (abs_nonneg _) (hrad i j)
      _ = Zonotope.radiusReach IM Z i := rfl
  have hreachnn : ∀ i, 0 ≤ Zonotope.radiusReach IM Z i :=
    fun i => (abs_nonneg _).trans (herrb i)
  -- the witness: the old coefficients, plus one per coordinate scaled to that reach
  refine Zonotope.mem_construct_iff.mpr
    ⟨Fin.append β (fun i => Zonotope.coefficient (Zonotope.radiusReach IM Z i) (err i)),
    ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ l
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hreachnn i) (herrb i)
  · rw [Zonotope.aux_sum_univ_mtimesIntervalMat]
    simp only [Zonotope.mtimesIntervalMat, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (herrb i)]
    -- centre acts exactly, and the leftover is `err`
    have hcentre : ∑ l, (IM.center *ᵥ Z.G l) i * β l
        = ∑ j, IM.center i j * (∑ l, Z.G l j * β l) := by
      simp_rw [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    rw [hcentre]
    have hsplit : (A *ᵥ x) i = (∑ j, IM.center i j * x j) + err i := by
      simp only [herr, Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hcx : ∑ j, IM.center i j * x j
        = (IM.center *ᵥ Z.c) i + ∑ j, IM.center i j * (∑ l, Z.G l j * β l) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hx j]; ring
    rw [hsplit, hcx]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
