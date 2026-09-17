import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.ofPoint`

CORA's `zonotope` at a centre and no generators: a single point, as the
representation. What `OfPoint` asks every representation with a point
operation to supply.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as a zonotope with no generators. -/
def Zonotope.ofPoint (v : α) : Zonotope α := ⟨0, v, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
