import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy

/-!
# Boxing what a partition drops over-approximates

The whole argument behind every reduction rule, and it holds at *every*
partition, which is what lets the ranking be a heuristic — Girard's metric
appears nowhere below.

Kept generators keep their coefficients; the dropped ones contribute `D` in row
`i`, which the diagonal block reproduces with coefficient `D / R` for `R` that
row's box radius. `hbound` bounds `|D|` by `R`, so the coefficient is
admissible, and `coefficient` handles the rescaling, degenerate `R = 0`
included.

`Partition.sum_split₂` is where the partition pays: the sum over all generators
splits into kept and dropped with no side condition.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing what a partition drops over-approximates, whichever partition it is. -/
theorem Zonotope.reduceBy_outer (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    Z.construct ⊆ (Z.reduceBy part).construct := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_construct_iff.mp hxmem
  have hbound : ∀ i, |∑ l, Z.G (part.right l) i * β (part.right l)|
      ≤ ∑ l, |Z.G (part.right l) i| := by
    intro i
    calc |∑ l, Z.G (part.right l) i * β (part.right l)|
        ≤ ∑ l, |Z.G (part.right l) i * β (part.right l)|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |Z.G (part.right l) i| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |Z.G (part.right l) i|                      := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l))
            (abs_nonneg (Z.G (part.right l) i))
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |Z.G (part.right l) i| :=
    fun i => (abs_nonneg _).trans (hbound i)
  -- the witness: kept coefficients, plus one per coordinate scaled to the dropped reach
  refine Zonotope.mem_construct_iff.mpr
    ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      Zonotope.coefficient (∑ l, |Z.G (part.right l) i|)
        (∑ l, Z.G (part.right l) i * β (part.right l))), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  · rw [hx i, part.sum_split₂ fun j => Z.G j i * β j, Zonotope.sum_univ_reduceBy]
    simp only [Zonotope.reduceBy, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
