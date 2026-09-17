import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.Global.LinProg.API

/-!
# `HPolytope.ofBounds`

A halfspace description built from a list of directions and a certified bound
for each. This is the shape of every operation a halfspace description cannot
perform exactly: the directions are the caller's choice — CORA's template
directions — and the right-hand side is whatever the certificates say, so
soundness never depends on the choice and only precision does.

Nothing here solves a linear program. It consumes the answers.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {S : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.ofBounds (Aq : Fin q → (α →ₗ[ℝ] ℝ)) (u : ∀ i, SupportBound S (Aq i)) :
    HPolytope α where
  m := q
  A := Aq
  b := fun i => (u i).val
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
