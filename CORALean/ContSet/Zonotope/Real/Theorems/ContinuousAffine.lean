import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The map a zonotope is the image of is continuous

Coefficients enter linearly, so `β ↦ c + ∑ βⱼ • Gⱼ` is continuous. It is what
carries compactness from the coefficient cube onto the set, both here and for
the constrained zonotope, whose `construct` is the image of its own domain under
this same map.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.continuous_affine (Z : Zonotope α) :
    Continuous fun β : Fin Z.h → ℝ => Z.c + ∑ j, β j • Z.G j :=
  continuous_const.add (continuous_finsetSum _ fun j _ =>
    (continuous_apply j).smul continuous_const)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
