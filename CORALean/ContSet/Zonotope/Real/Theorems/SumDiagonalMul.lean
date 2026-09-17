import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A diagonal block of generators couples each coordinate to one coefficient

What moves an interval box into generators: off the diagonal every product
vanishes, so a sum over the block collapses to a single term. The same fact
read down a column is `SumDiagonalMulCol.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A diagonal block couples each coordinate to one coefficient and no other. -/
theorem Zonotope.sum_diagonal_mul (v g : Vec ℝ n) (i : Fin n) :
    ∑ i', Matrix.diagonal v i i' * g i' = v i * g i := by -- --- PROOF ---
  rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne' _ hb, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
