import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.map`

A linear map applies to centre and generators alike, which is why a zonotope is
closed under one and the generator count is untouched.

Every multiplication a zonotope carries is this at a particular map — `mtimes`
at `A *ᵥ ·`, matrix multiplication at `A * ·` or `· * A` — so none of them needs
an exactness proof of its own.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.map (f : α →ₗ[ℝ] β) (Z : Zonotope α) : Zonotope β where
  h := Z.h
  c := f Z.c
  G := fun j => f (Z.G j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
