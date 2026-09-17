import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
import CORALean.Global.Float.EuclideanNorm
import CORALean.Global.Sort

/-!
# `Zonotope.reduceCombastel`

Combastel's metric is `sqSumUp`, `Global.Float.EuclideanNorm`'s squared length:
no square root to call, and squaring changes no ranking, since it is monotone
on the nonnegatives a length is.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Combastel's metric on one generator: `sqSumUp`'s squared length, rounded up.
Squaring avoids `Real.sqrt`, absent from `FloatOps`, and keeps the ranking,
monotone on the nonnegatives a length is. -/
def Zonotope.aux_combastelMetric (Z : Zonotope 𝕋 n) (j : Fin Z.h) : 𝕋 :=
  sqSumUp fun i => Z.G i j

/-- The generators Combastel's rule keeps at order `o`, against the rest:
`(o-1)*n` of them, leaving room for the box of `n`. The comparator ranks the
larger metric first, so the largest-magnitude generators survive. -/
def Zonotope.aux_combastelSplit (Z : Zonotope 𝕋 n) (o : ℕ) (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) ⊕ (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((sortPerm fun j₁ j₂ => le (Z.aux_combastelMetric j₂) (Z.aux_combastelMetric j₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'combastel', o)`: keep the `(o - 1) * n` largest-magnitude
generators and box the rest, which brings the count to `o * n`. Already at
that order or below, nothing happens. -/
def Zonotope.reduceCombastel (Z : Zonotope 𝕋 n) (o : ℕ) : Zonotope 𝕋 n :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.aux_combastelSplit o hlt) else Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
