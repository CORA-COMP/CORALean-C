import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `Zonotope.girardSplit`

Girard's metric, `‖g‖₁ - ‖g‖∞`, measures what boxing a generator costs
directly, zero on an axis-aligned one. The split it drives keeps the `(o-1)*n`
generators dearest to box and passes the rest on to be boxed.

A definition of its own rather than a helper inside `reduceGirard`: one
partition says both what the reduction keeps and what its error box absorbs, so
`reduceGirard` and `reduceBox` read the same one from here.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`. Zero exactly on the
axis-aligned generators, which a box reproduces for free, and growing with what
boxing would cost; the max folds from `0`, which no `|G i j|` undercuts. -/
noncomputable def Zonotope.aux_girardMetric (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  (∑ i, |Z.G j i|) - Finset.univ.fold max 0 fun i => |Z.G j i|


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators Girard's rule keeps at order `o`, against the rest: `(o-1)*n`
of them, leaving room for the box of `n`. Sorting is ascending, so the metric
enters negated and the generators dearest to box rank first, as CORA's do. -/
noncomputable def Zonotope.girardSplit (Z : Zonotope (Vec ℝ n)) (o : ℕ) (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) ⊕ (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((Tuple.sort fun j => -Z.aux_girardMetric j).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
