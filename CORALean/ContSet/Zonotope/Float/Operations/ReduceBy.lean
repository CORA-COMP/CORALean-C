import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Global.Partition

/-!
# `Zonotope.reduceBy`

CORA's reduction at a given partition, unchanged in shape and sound for every
one of them. Nothing is charged to the box: the centre and kept generators are
copied exactly, and the diagonal block rounds *up*, which only enlarges.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's reduction at a given partition, unchanged in shape and sound for
every one of them. Nothing is charged to the box: the centre and kept generators
are copied exactly, and the diagonal block rounds *up*, which only enlarges. -/
def Zonotope.reduceBy (Z : Zonotope 𝕋 n) (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    Zonotope 𝕋 n where
  h := q + n
  c := Z.c
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                  (diagonalBlock (radius fun i l => Z.G i (part.right l)) i)
  E := Z.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
