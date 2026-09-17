import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Global.Sort

/-!
# `Zonotope.girardSplit`

Girard's metric, `‖g‖₁ - ‖g‖∞`, measures what boxing a generator costs
directly, zero on an axis-aligned one; `Tuple.sort` wants a `LinearOrder`,
which no float type has — distinct representations of one value compare equal
each way, so antisymmetry fails — hence `sortPerm`, which asks its comparator
for nothing. It can afford to, since `reduceBy_outer` holds at every
partition: a misranking costs precision alone.

A definition of its own rather than a helper inside `reduceGirard`, as at
`Real`: one partition says both what the reduction keeps and what its error
box absorbs, so `reduceGirard` and `reduceGirardBox` read the same one from
here.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`. Zero exactly on the
axis-aligned generators, which a box reproduces for free. -/
def Zonotope.aux_girardMetric (Z : Zonotope 𝕋 n) (j : Fin Z.h) : 𝕋 :=
  subDown (sumUp fun i => absolute (Z.G i j)) (maximumOver fun i => absolute (Z.G i j))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators Girard's rule keeps at order `o`, against the rest: `(o-1)*n`
of them, leaving room for the box of `n`. The comparator ranks the larger metric
first, so the generators dearest to box survive — CORA's descending sort. -/
def Zonotope.girardSplit (Z : Zonotope 𝕋 n) (o : ℕ) (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) ⊕ (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((sortPerm fun j₁ j₂ => le (Z.aux_girardMetric j₂) (Z.aux_girardMetric j₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
