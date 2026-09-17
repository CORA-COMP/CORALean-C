import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.MinkDiffInner
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsCompact

/-!
# What `Interval` instantiates

The same obligations the exact layer discharges, since a float interval denotes a
set of real points just as an exact one does; only the scalar the operations run
in differs. `ConvexSet` and `CompactSet` cost no float proof: `construct` is
`nominal.construct` by definition, so the exact layer's theorems apply to
`I.nominal` unchanged. `Intersection` is exact here too, nothing rounding.

`reduce` gives up no order, as over ℝ: an interval has none to give up. No
`OfPoint`: it would round a real point into `𝕋`, an operation this layer lacks.

Every field returns a `materialise`d interval. The bounds are function types, so
the one an operation returns is a closure over the one it was given, and a loop
that iterates operations would rebuild its whole history on every read.
`materialise_eq` is the identity, so each proof below is the operation's own
guarantee after one rewrite. It is here rather than in `Operations/` because this
is where a set is handed back to a caller that may loop.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (Interval 𝕋 n) (Vec ℝ n) := ⟨Interval.construct⟩

instance : ConvexSet (Interval 𝕋 n) (Vec ℝ n) := ⟨fun I => I.nominal.convex_construct⟩

instance : CompactSet (Interval 𝕋 n) (Vec ℝ n) := ⟨fun I => I.nominal.isCompact_construct⟩

instance : Plus (Interval 𝕋 n) (Vec ℝ n) where
  plus I₁ I₂ := (Interval.plus I₁ I₂).materialise
  plus_outer I₁ I₂ := by
    rw [Interval.materialise_eq]
    exact Interval.plus_outer I₁ I₂

instance : MinkDiff (Interval 𝕋 n) (Vec ℝ n) where
  minkDiff I₁ I₂ := (Interval.minkDiff I₁ I₂).materialise
  minkDiff_inner I₁ I₂ := by
    rw [Interval.materialise_eq]
    exact Interval.minkDiff_inner I₁ I₂

instance : Intersection (Interval 𝕋 n) (Vec ℝ n) where
  intersection := Interval.intersection
  intersection_outer I₁ I₂ := (Interval.intersection_exact I₁ I₂).symm.subset

instance : LinComb (Interval 𝕋 n) (Vec ℝ n) where
  linComb I₁ I₂ := (Interval.linComb I₁ I₂).materialise
  linComb_outer I₁ I₂ := by
    rw [Interval.materialise_eq]
    exact Interval.linComb_outer I₁ I₂

/-- Nothing to reduce — a box is its own order — so this is storage and no more,
which is exactly what a loop calling `reduce` every step wants of it. -/
instance : Reduce (Interval 𝕋 n) (Vec ℝ n) where
  reduce I _ := I.materialise
  reduce_outer I _ := by
    rw [Interval.materialise_eq]

/-- The one field here that is an equality: a relabelling does no arithmetic, so
the float box loses exactly what the exact one does, namely nothing. -/
instance : Reindex (Interval 𝕋) where
  reindex e I := (Interval.reindex e I).materialise
  reindex_exact e I := by
    rw [Interval.materialise_eq]
    exact Interval.reindex_exact e I

instance : Mtimes (Mat 𝕋) (Interval 𝕋) where
  mtimes M I := (Interval.mtimes M I).materialise
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, Interval.materialise_eq]
    exact Interval.mtimes_outer M I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
