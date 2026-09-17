import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.ineqs`, over a floating-point scalar

CORA's inequality constructor. Absorbs its rounding by raising `b`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.ineqs (A : Mat 𝕋 q n) (b : Vec 𝕋 q) : HPolytope 𝕋 n where
  m := q
  A := A
  b := b
  me := 0
  Ae := fun i => i.elim0
  be := ⟨fun i => i.elim0, fun i => i.elim0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
