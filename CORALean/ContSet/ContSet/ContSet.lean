import CORALean.Global.Scalar

/-!
# Set representations

CORA's `contSet`: one field, `construct`, sending a representation to the set it
denotes. The set is always over ℝ, whichever arithmetic the representation
computes in, so over-approximation and refinement are the one relation
`X ⊆ construct s` and compose by transitivity.

The operation classes stay separate from `ContSet`, since `construct` is
meaningful at strictly more types than the operations are: a zonotope denotes a
set over any real module, but `reduce` needs coordinates, and a plain matrix
denotes the singleton it is without being closed under anything.

`Mtimes` and `Reindex` keep a family indexed by ℕ, being the operations that
move between ambient types, where the result has to land somewhere.

A precision parameter stays out of the classes: an operand-independent one is
closed over by a `def` returning the class, as `Ellipsoid.plusInstance` does; an
operand-dependent one needs an oracle a total `plus : S → S → S` cannot have.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   11-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise


-- ========================================  MAIN TYPE  ========================================= --

class ContSet (S : Type) (α : outParam Type) where
  construct : S → Set α

open ContSet

/-- `x ∈ s` for a representation means what it denotes. -/
instance {S α : Type} [ContSet S α] : Membership α S := ⟨fun s x => x ∈ construct s⟩

theorem ContSet.mem_iff {S α : Type} [ContSet S α] {s : S} {x : α} :
    x ∈ s ↔ x ∈ construct s := Iff.rfl

open Scalar

/-- A matrix denotes itself, read into ℝ by the layer's scalar. What makes a
statement about a set of matrices cover the plain one. -/
instance {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} : ContSet (Mat 𝕋 m n) (Mat ℝ m n) where
  construct M := {toRealMat M}

@[simp] theorem ContSet.construct_mat {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} (M : Mat 𝕋 m n) :
    construct M = {toRealMat M} := rfl

/-- The set of linear maps `α → β` that `M` denotes. `α` is an input and only
`β` an `outParam`, so one matrix type acts on several ambient types, the
instances told apart by the type it is applied at. -/
class LinMapSet (M : Type) (α : Type) (β : outParam Type)
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β] where
  denote : M → Set (α →ₗ[ℝ] β)

/-- Left multiplication by a matrix, on matrices. -/
def matMulLeft {p q r : ℕ} (M : Mat ℝ p q) : Mat ℝ q r →ₗ[ℝ] Mat ℝ p r where
  toFun B := M * B
  map_add' := Matrix.mul_add M
  map_smul' c B := Matrix.mul_smul M c B

/-- Right multiplication by a matrix, on matrices. -/
def matMulRight {p q r : ℕ} (M : Mat ℝ q r) : Mat ℝ p q →ₗ[ℝ] Mat ℝ p r where
  toFun B := B * M
  map_add' B C := Matrix.add_mul B C M
  map_smul' c B := Matrix.smul_mul c B M

/-- Matrix multiplication as a bilinear map, which is what a set-valued product
of two matrix representations is taken at. -/
def matMulBilin {p q r : ℕ} : Mat ℝ p q →ₗ[ℝ] Mat ℝ q r →ₗ[ℝ] Mat ℝ p r where
  toFun := matMulLeft
  map_add' A B := LinearMap.ext fun C => Matrix.add_mul A B C
  map_smul' c A := LinearMap.ext fun C => Matrix.smul_mul c A C

@[simp] theorem matMulBilin_apply {p q r : ℕ} (A : Mat ℝ p q) (B : Mat ℝ q r) :
    matMulBilin A B = A * B := rfl

/-- A matrix acting on vectors. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q : ℕ} : LinMapSet (Mat 𝕋 p q) (Vec ℝ q) (Vec ℝ p) where
  denote M := {Matrix.mulVecLin (toRealMat M)}

/-- The same matrix acting on matrices, from the left. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q r : ℕ} :
    LinMapSet (Mat 𝕋 p q) (Mat ℝ q r) (Mat ℝ p r) where
  denote M := {matMulLeft (toRealMat M)}

/-- Multiplication by anything denoting matrices, covering the interval matrix a
discretization produces as well as the plain one. The guarantee is over
everything the argument denotes, which at a plain matrix is the one map it is. -/
class Mtimes (𝕄 : ℕ → ℕ → Type) (S : ℕ → Type)
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] where
  mtimes {m n : ℕ} : 𝕄 m n → S n → S m
  mtimes_outer {m n : ℕ} (M : 𝕄 m n) (s : S n) :
    (⋃ A ∈ construct M, (A *ᵥ ·) '' construct s) ⊆ construct (mtimes M s)

/-- Relabelling coordinates, bundled: a reindexing is a linear map, which is
what lets a representation closed under `map` discharge the guarantee below with
the exactness proof it already has. -/
def reindexLin {n m : ℕ} (e : Fin m ≃ Fin n) : Vec ℝ n →ₗ[ℝ] Vec ℝ m where
  toFun x := fun i => x (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reading a set's coordinates in a different order, the one class here whose
guarantee is an *equality* — which is what a reshape layer needs. An equivalence
and not a plain function: a box cannot constrain two copies of a coordinate. -/
class Reindex (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  reindex {n m : ℕ} : (Fin m ≃ Fin n) → S n → S m
  reindex_exact {n m : ℕ} (e : Fin m ≃ Fin n) (s : S n) :
    construct (reindex e s) = reindexLin e '' construct s

/-- Every point on a segment running from one set to the other: [1, Def. 7],
which writes the parameter over `[-1,1]` and calls the result a convex hull — it
is one only where both sets are convex. -/
def segments {α : Type} [AddCommGroup α] [Module ℝ α] (X Y : Set α) : Set α :=
  {x | ∃ y₁ ∈ X, ∃ y₂ ∈ Y, ∃ lam ∈ Set.Icc (0:ℝ) 1, x = lam • y₁ + (1 - lam) • y₂}

/-- Every point from which anything in `T` still lands in `S`: `plus`'s
guarantee, run in reverse. -/
def minkowskiDiff {α : Type} [AddCommGroup α] [Module ℝ α] (S T : Set α) : Set α :=
  {x | ∀ y ∈ T, x + y ∈ S}

/-- CORA's `plus`, outer only, so a proof against it says nothing about how much
precision the representation loses. Ambient type in and out, so an algorithm
that also travels between dimensions asks for `Mtimes` on top. -/
class Plus (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  plus : S → S → S
  plus_outer (s₁ s₂ : S) :
    construct s₁ + construct s₂ ⊆ construct (plus s₁ s₂)

/-- CORA's intersection, outer even though five of six implementations are
exact: an intersection is a set an algorithm computes, and `VPolytope`'s goes
through a halfspace round trip that only encloses, never exactly. -/
class Intersection (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  intersection : S → S → S
  intersection_outer (s t : S) : construct s ∩ construct t ⊆ construct (intersection s t)

/-- CORA's Minkowski difference. The opposite of `Plus`: a difference is a
*guarantee*, so an implementation may only ever *under*-approximate — never
over — and the obligation below is an **inner**, not an outer, inclusion. -/
class MinkDiff (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  minkDiff : S → S → S
  minkDiff_inner (s t : S) : construct (minkDiff s t) ⊆ minkowskiDiff (construct s) (construct t)

/-- CORA's `linComb`, not the convex hull: the two agree only when both sets are
convex, and this is what keeps a non-convex representation non-convex. -/
class LinComb (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  linComb : S → S → S
  linComb_outer (s₁ s₂ : S) :
    segments (construct s₁) (construct s₂) ⊆ construct (linComb s₁ s₂)

/-- A singleton, as a set of the representation. -/
class OfPoint (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  ofPoint : α → S
  mem_ofPoint (v : α) : v ∈ construct (ofPoint v)

/-- A set taken apart into a point of the ambient space and a set holding the
origin. Every representation with a centre has this; no class offered it. -/
class Recentre (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  centre : S → α
  recentre : S → S
  zero_mem_recentre (s : S) : (0 : α) ∈ construct (recentre s)
  sub_centre_mem_recentre {s : S} {y : α} (hy : y ∈ construct s) :
    y - centre s ∈ construct (recentre s)

/-- To a maximum order, read in the representation's own terms. Sound for any
target, so the order is a precision knob and never a correctness one. -/
class Reduce (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  reduce : S → ℕ → S
  reduce_outer (s : S) (o : ℕ) :
    construct s ⊆ construct (reduce s o)

-- No class bundles these: a representation with no `linComb` still runs what never combines.

/-- CORA's symbol for the Minkowski sum, deliberately not `+`: `plus` is only
*outer*, and with `Pointwise` open the two would otherwise look alike. -/
scoped infixl:65 " ⊞ " => Plus.plus

-- No `class abbrev` for these binders: each use adds an unfolding step and times out search.

/-- Multiplication by anything denoting linear maps, at any pair of ambient
types. `Mtimes` is this at vectors, kept separate because there the dimension
moves and the family index is what says where the result lands. -/
class LinMtimes (M S : Type) (T : outParam Type) (α : outParam Type) (β : outParam Type)
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    [ContSet S α] [ContSet T β] [LinMapSet M α β] where
  lmtimes : M → S → T
  lmtimes_outer (m : M) (s : S) :
    (⋃ f ∈ LinMapSet.denote (β := β) m, f '' construct s) ⊆ construct (lmtimes m s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
