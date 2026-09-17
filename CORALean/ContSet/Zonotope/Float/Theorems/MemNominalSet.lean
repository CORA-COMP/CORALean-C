import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct

/-!
# Membership in the nominal zonotope, in the stored fields

Every enclosure proof at this layer splits a point into a nominal part and an
error, and this is the form it reads the nominal part in: the exact layer's
coordinatewise membership with the stored floats put through `toReal`.

Proofs use it rather than going through `nominal` because through it every
count is `Z.h`, where the instance gives the equal-but-distinct `(nominal Z).h`
that `rw` reads apart.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- definitionally the exact layer's reading, the generators already transposed
theorem Zonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {Z : Zonotope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet Z ↔ ∃ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) ∧
      ∀ i, x i = toReal (Z.c i) + ∑ j, toReal (Z.G i j) * β j :=
  Real.Zonotope.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
