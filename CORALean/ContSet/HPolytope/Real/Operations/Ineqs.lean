import CORALean.ContSet.HPolytope.Real.Operations.RowLin

/-!
# `HPolytope.ineqs`

CORA's `polytope(A, b)`: one inequality per row.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `polytope(A, b)`: one inequality per row. -/
def HPolytope.ineqs (A : Mat ℝ q n) (b : Vec ℝ q) : HPolytope (Vec ℝ n) where
  m := q
  A := HPolytope.rowLin A
  b := b
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
