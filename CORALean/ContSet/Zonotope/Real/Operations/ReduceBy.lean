import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Partition

/-!
# `Zonotope.reduceBy`

Keeps the generators a partition names and boxes the rest into a diagonal
block, one entry per absorbed row's `1`-norm. CORA's twenty-odd reduction rules
are this definition with a different partition.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Partitions the generator indices rather than choosing them: `part.left` is
kept, `part.right` absorbed into a diagonal block. CORA's twenty-odd selection
rules are this definition with a different partition. -/
def Zonotope.reduceBy (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Zonotope (Vec ℝ n) where
  h := q + n
  c := Z.c
  G := Fin.append (fun l => Z.G (part.left l))
        (Matrix.diagonal fun i => ∑ l, |Z.G (part.right l) i|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
