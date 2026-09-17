import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.recentre`

CORA's `zonotope` with `c` zeroed: the same generators, moved to hold the
origin instead of the centre. What `Recentre` asks a representation with a
centre to supply, alongside `Zonotope.c` itself as `centre`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope moved to the origin, keeping its generators. -/
def Zonotope.recentre (Z : Zonotope α) : Zonotope α := ⟨Z.h, 0, Z.G⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
