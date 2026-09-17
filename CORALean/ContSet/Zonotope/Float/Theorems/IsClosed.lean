import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact

/-!
# A float zonotope is closed

Read off compactness, as over ℝ: the sum of the nominal set and the error box
is an affine image of a product of cubes, and an affine image of a merely
closed set need not be closed. Closedness on its own is what a bundle's
compactness asks of each member.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isClosed_construct (Z : Zonotope 𝕋 n) : IsClosed Z.construct :=
  Z.isCompact_construct.isClosed

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
