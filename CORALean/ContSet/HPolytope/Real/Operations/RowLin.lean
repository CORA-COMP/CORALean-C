import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.rowLin`

Row `i` of a constraint matrix, as the functional a constraint is. Only here
does a constraint become a matrix row, and only at `Vec` — the representation
itself needs no coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` of `M`, as the functional a constraint is. Named rather than
file-local: the float layer states its own bounds against these rows. -/
def HPolytope.rowLin (M : Mat ℝ q n) (i : Fin q) : Vec ℝ n →ₗ[ℝ] ℝ where
  toFun x := (M *ᵥ x) i
  map_add' x y := by rw [Matrix.mulVec_add]; rfl
  map_smul' c x := by rw [RingHom.id_apply, Matrix.mulVec_smul]; rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
