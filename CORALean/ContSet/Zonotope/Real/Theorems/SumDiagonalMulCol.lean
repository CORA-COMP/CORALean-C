import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A diagonal block of generators, read down a column

Split out of `SumDiagonalMul.lean` (issue #62): the same fact read down a
column instead of along a row, which is the form a diagonal block takes when
generators carry the first index.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same read down a column, which is the form a diagonal block takes when
generators carry the first index. -/
theorem Zonotope.sum_diagonal_mul' (v g : Vec ℝ n) (i : Fin n) :
    ∑ l, Matrix.diagonal v l i * g l = v i * g i := by -- --- PROOF ---
  rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ hb, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
