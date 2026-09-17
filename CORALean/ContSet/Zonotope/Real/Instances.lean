import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.WithEmpty.WithEmpty
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.LmtimesSingletonOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyInner
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesMatZonotopeOuter
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreZeroMem
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# What `Zonotope` instantiates

Each obligation is a theorem from `Theorems`, the exact ones read in the `⊆`
direction.

Noncomputable, as `reduce` is: it ranks generators, and ordering reals cannot be
computed.

`MinkDiff` is the one instance not at `Zonotope` itself. Every zonotope holds
its centre and a difference can be empty, so no total operation into `Zonotope`
meets that class's obligation; at `WithEmpty (Zonotope α)` it does, `empty`
being the answer where no generator representation certifies one.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- At every ambient type, not only `Vec`: what a zonotope denotes needs no
coordinates. The operation instances below stay at `Vec`, because `reduce`
does. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (Zonotope α) α :=
  ⟨Zonotope.construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ConvexSet (Zonotope α) α :=
  ⟨Zonotope.convex_construct⟩

/-- Compactness, not the closed-and-bounded pair: an affine image of the
coefficient cube is what a zonotope is, and only compactness survives it. -/
instance {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] : CompactSet (Zonotope α) α :=
  ⟨Zonotope.isCompact_construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : OfPoint (Zonotope α) α where
  ofPoint := Zonotope.ofPoint
  mem_ofPoint := Zonotope.mem_ofPoint

/-- `centre` is `Zonotope.c` directly: a field projection needs no operation
of its own. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : Recentre (Zonotope α) α where
  centre Z := Z.c
  recentre := Zonotope.recentre
  zero_mem_recentre := Zonotope.zero_mem_recentre
  sub_centre_mem_recentre := Zonotope.sub_centre_mem_recentre

instance : Plus (Zonotope (Vec ℝ n)) (Vec ℝ n) where
  plus := Zonotope.plus
  plus_outer Z₁ Z₂ := (Zonotope.plus_exact Z₁ Z₂).subset

noncomputable instance : LinComb (Zonotope (Vec ℝ n)) (Vec ℝ n) where
  linComb := Zonotope.linComb
  linComb_outer := Zonotope.linComb_outer

noncomputable instance : Reduce (Zonotope (Vec ℝ n)) (Vec ℝ n) where
  reduce := Zonotope.reduce
  reduce_outer := Zonotope.reduce_outer

/-- `map` at the relabelling, and no operation of its own: a reindexing *is* a
linear map, and a zonotope is exactly closed under one. -/
instance : Reindex (fun n => Zonotope (Vec ℝ n)) where
  reindex e Z := Zonotope.map (reindexLin e) Z
  reindex_exact e Z := (Zonotope.map_exact (reindexLin e) Z).symm

instance : Mtimes (Mat ℝ) (fun n => Zonotope (Vec ℝ n)) where
  mtimes := Zonotope.mtimes
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Zonotope.mtimes_exact M Z).subset

/-- The zonotope family over vectors. A generic theorem quantifies over
`S : ℕ → Type` and the elaborator cannot read that family off one member, so a
use site has to name it: `(S := 𝒵)`. -/
scoped notation "𝒵" => fun n => Zonotope (Vec ℝ n)

-- the five-parameter `LinMtimes` header re-runs instance search on `Mat` and `Vec`
set_option maxHeartbeats 400000 in
/-- Multiplication by a plain matrix at any ambient type it acts on. At `Vec`
this repeats `mtimes`; at `Mat` it is matrix multiplication of a matrix
zonotope, which needs no development of its own. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q : ℕ} :
    LinMtimes (Mat 𝕋 p q) (Zonotope (Vec ℝ q)) (Zonotope (Vec ℝ p)) (Vec ℝ q) (Vec ℝ p) where
  lmtimes M Z := Zonotope.mapOf (Matrix.mulVecLin (Scalar.toRealMat M)) Z
  lmtimes_outer _M Z := Zonotope.lmtimes_singleton_outer _ Z

-- the same header at `Mat ℝ q r`, where `matMulLeft` adds another module instance to find
set_option maxHeartbeats 400000 in
instance {𝕋 : Type} [Scalar 𝕋] {p q r : ℕ} :
    LinMtimes (Mat 𝕋 p q) (Zonotope (Mat ℝ q r)) (Zonotope (Mat ℝ p r))
      (Mat ℝ q r) (Mat ℝ p r) where
  lmtimes M Z := Zonotope.mapOf (matMulLeft (Scalar.toRealMat M)) Z
  lmtimes_outer _M Z := Zonotope.lmtimes_singleton_outer _ Z

/-- The same operation at an interval matrix, which no other class asks
for: a zonotope carries it, and a discretization is what wants it. -/
noncomputable instance :
    Mtimes ℐ 𝒵 where
  mtimes := Zonotope.mtimesIntervalMat
  mtimes_outer IM Z := by
    exact Zonotope.mtimesIntervalMat_outer IM Z

/-- The matrix-zonotope family: CORA's `matZonotope`, per `Zonotope.lean`'s
docstring, not a representation of its own. -/
scoped notation "𝕄𝒵" => fun m n => Zonotope (Mat ℝ m n)

/-- Multiplying a set by a matrix zonotope: CORA's `matZonotope * zonotope`. -/
noncomputable instance : Mtimes 𝕄𝒵 𝒵 where
  mtimes := Zonotope.mtimesMatZonotope
  mtimes_outer M Z := Zonotope.mtimesMatZonotope_outer M Z

/-- Not at `Zonotope α`: `{0} ⊖ [-1, 1]` is `∅`, which no zonotope denotes, so
the wrapper is where a total difference can live. -/
noncomputable instance {α : Type} [AddCommGroup α] [Module ℝ α] :
    MinkDiff (WithEmpty (Zonotope α)) α where
  minkDiff s t := match s, t with
    | .of Z₁, .of Z₂ => Z₁.minkDiffOrEmpty Z₂
    | _, _ => .empty
  minkDiff_inner s t := by
    cases s <;> cases t
    -- only the pair of zonotopes has anything to prove; `∅` discharges the rest
    case of.of Z₁ Z₂ =>
      show ContSet.construct (Z₁.minkDiffOrEmpty Z₂) ⊆ _
      cases hE : Z₁.minkDiffOrEmpty Z₂ with
      | empty => exact Set.empty_subset _
      | of D => exact Zonotope.minkDiffOrEmpty_inner Z₁ Z₂ hE
    all_goals exact Set.empty_subset _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
