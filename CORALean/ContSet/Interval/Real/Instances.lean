import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.Interval.Real.Operations.IntersectionExact
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsCompact
import CORALean.ContSet.Interval.Real.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Real.Theorems.MinkDiffExact
import CORALean.ContSet.Interval.Real.Theorems.PlusExact
import CORALean.ContSet.Interval.Real.Theorems.ReindexExact

/-!
# What `Interval` instantiates

`reduce` is the identity: an interval holds two bounds per coordinate whatever
order is asked for, so it has nothing to give up.

`ConvexSet` and `CompactSet` are what carry a box to the reachability statements
that read their topological hypotheses off the representation instead of taking
them per use. Convexity holds at every ambient type with coordinates;
compactness only at `Vec`, which is where boundedness is stated.

No `Recentre`: it asks `0 ∈ construct (recentre s)` unconditionally, and a
crossed box denotes `∅`, holding nothing at all. `Theorems/RecentreZeroMem`
and `RecentreSubMem` carry the nonemptiness this class refuses to ask for.

`Intersection` too, coordinatewise and exact: intersecting two boxes takes the pointwise
max of the lower bounds and the pointwise min of the upper ones.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- At every ambient type that has coordinates, so an interval matrix is an
instance too. The operation instances below are stated only at `Vec`, which is
where an algorithm asks for them. -/
instance {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι] :
    ContSet (Interval α) α := ⟨Interval.construct⟩

instance {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι] :
    ConvexSet (Interval α) α := ⟨Interval.convex_construct⟩

/-- At `Vec ℝ n` alone: closedness and boundedness are read coordinatewise, but
the norm they bound is not, so the ambient type has to be one the coordinates
determine. -/
instance : CompactSet (Interval (Vec ℝ n)) (Vec ℝ n) := ⟨Interval.isCompact_construct⟩

instance {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι] :
    OfPoint (Interval α) α where
  ofPoint := Interval.point
  mem_ofPoint := Interval.mem_point

instance : Plus (Interval (Vec ℝ n)) (Vec ℝ n) where
  plus := Interval.plus
  plus_outer := Interval.plus_outer

instance : MinkDiff (Interval (Vec ℝ n)) (Vec ℝ n) where
  minkDiff := Interval.minkDiff
  minkDiff_inner := Interval.minkDiff_inner

instance : Intersection (Interval (Vec ℝ n)) (Vec ℝ n) where
  intersection := Interval.intersection
  intersection_outer I₁ I₂ := (Interval.intersection_exact I₁ I₂).symm.subset

instance : LinComb (Interval (Vec ℝ n)) (Vec ℝ n) where
  linComb := Interval.linComb
  linComb_outer := Interval.linComb_outer

instance : Reduce (Interval (Vec ℝ n)) (Vec ℝ n) where
  reduce I _ := I
  reduce_outer _ _ := subset_rfl

/-- The one instance here whose field is an equality: a reshape layer's content
is that it loses nothing, and `Mtimes` at a permutation matrix has no room to
say so. -/
instance : Reindex (fun n => Interval (Vec ℝ n)) where
  reindex := Interval.reindex
  reindex_exact := Interval.reindex_exact

instance : Mtimes (Mat ℝ) (fun n => Interval (Vec ℝ n)) where
  mtimes := Interval.mtimes
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Interval.mtimes_outer M I

/-- The interval-matrix family. A generic theorem quantifies over `𝕄 : ℕ → ℕ → Type`
and the elaborator cannot read that family off one member, so a use site has to
name it: `(𝕄 := ℐ)`. -/
scoped notation "ℐ" => fun m n => Interval (Mat ℝ m n)

/-- The interval-vector family, `ℐ` being already the matrix one: pins `(S := ℐ𝒱)`
where a generic theorem cannot read the family off one member. -/
scoped notation "ℐ𝒱" => fun n => Interval (Vec ℝ n)

/-- The same operation at an interval matrix, which a discretization wants. A
box needs no fresh generator to absorb the radius: the four corner products
already bound each term, so the result is a box of the same shape. -/
instance : Mtimes ℐ (fun n => Interval (Vec ℝ n)) where
  mtimes := Interval.mtimesIntervalMat
  mtimes_outer IM I := Interval.mtimesIntervalMat_outer IM I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
