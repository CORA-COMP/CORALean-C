import CORALean.Global.LinProg.LinProg

/-!
# How a bound travels across set operations

A direction sees a Minkowski sum as a sum of extents, a union as the larger of
two, a linear image as the direction pulled back through the map, and a convex
hull as no further than the points it was taken of. So one bound per operand is
enough, and a representation that can answer `SupportBound` for itself can be
enclosed after any of these without knowing how the result is described.

This is what makes the hard polytope operations definable: the enclosure is a
list of directions, and its right-hand side is assembled here.

What does *not* travel is an enclosure, and `exists_outer_without_supportBound`
is that: every operation class guarantees exactly `exact ⊆ computed`, and a
bound crosses an inclusion the other way, so a bound on `construct (plus s t)`
comes from the representation and never from bounds on the two operands.

`SupportWitness` travels the same way, `union`'s `max` now chosen by a case
split, since only one of the two points attains it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   15-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {S T : Set α} {c : α →ₗ[ℝ] ℝ}

def SupportBound.add (u : SupportBound S c) (v : SupportBound T c) :
    SupportBound (S + T) c where
  val := u.val + v.val
  le := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    show c (x + y) ≤ u.val + v.val
    rw [map_add]
    exact add_le_add (u.le x hx) (v.le y hy)

/-- Directions add, which is what makes an inexact dual solution usable: `c`
splits as `d + (c - d)`, the dual bounds `d`, and whatever it missed by is
bounded separately over an enclosure already in hand. -/
def SupportBound.addDir {d : α →ₗ[ℝ] ℝ} (u : SupportBound S c) (v : SupportBound S d) :
    SupportBound S (c + d) where
  val := u.val + v.val
  le x hx := by
    show c x + d x ≤ u.val + v.val
    exact add_le_add (u.le x hx) (v.le x hx)

def SupportBound.union (u : SupportBound S c) (v : SupportBound T c) :
    SupportBound (S ∪ T) c where
  val := max u.val v.val
  le x hx :=
    hx.elim (fun h => le_trans (u.le x h) (le_max_left _ _))
      fun h => le_trans (v.le x h) (le_max_right _ _)

/-- The image under `M` reaches as far in direction `c` as the source does in
direction `c ∘ M`, which is how a bound survives a change of space. -/
def SupportBound.image {d : β →ₗ[ℝ] ℝ} (M : α →ₗ[ℝ] β) (u : SupportBound S (d.comp M)) :
    SupportBound (M '' S) d where
  val := u.val
  le := by
    rintro _ ⟨x, hx, rfl⟩
    exact u.le x hx

def SupportBound.smul {r : ℝ} (hr : 0 ≤ r) (u : SupportBound S c) :
    SupportBound (r • S) c where
  val := r * u.val
  le := by
    rintro _ ⟨x, hx, rfl⟩
    show c (r • x) ≤ r * u.val
    rw [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (u.le x hx) hr

/-- Pointwise Minkowski sum, dual to `SupportBound.add`. -/
def SupportWitness.add (u : SupportWitness S c) (v : SupportWitness T c) :
    SupportWitness (S + T) c where
  val := u.val + v.val
  mem := by
    obtain ⟨x, hx, hu⟩ := u.mem
    obtain ⟨y, hy, hv⟩ := v.mem
    exact ⟨x + y, Set.add_mem_add hx hy, by rw [map_add]; exact add_le_add hu hv⟩

/-- The image under `M` witnesses at least as much in direction `d` as the
source does in direction `d ∘ M`, dual to `SupportBound.image`. -/
def SupportWitness.image {d : β →ₗ[ℝ] ℝ} (M : α →ₗ[ℝ] β) (u : SupportWitness S (d.comp M)) :
    SupportWitness (M '' S) d where
  val := u.val
  mem := by
    obtain ⟨x, hx, hu⟩ := u.mem
    exact ⟨M x, Set.mem_image_of_mem M hx, hu⟩

/-- Whichever witness is larger carries its own point across the union: dual to
`SupportBound.union`, chosen by a case split rather than handed to both sides. -/
def SupportWitness.union (u : SupportWitness S c) (v : SupportWitness T c) :
    SupportWitness (S ∪ T) c where
  val := max u.val v.val
  mem := by
    obtain ⟨x, hx, hu⟩ := u.mem
    obtain ⟨y, hy, hv⟩ := v.mem
    rcases le_total u.val v.val with h | h
    · exact ⟨y, Or.inr hy, by simpa [max_eq_right h] using hv⟩
    · exact ⟨x, Or.inl hx, by simpa [max_eq_left h] using hu⟩

def SupportWitness.smul {r : ℝ} (hr : 0 ≤ r) (u : SupportWitness S c) :
    SupportWitness (r • S) c where
  val := r * u.val
  mem := by
    obtain ⟨x, hx, hu⟩ := u.mem
    refine ⟨r • x, Set.smul_mem_smul_set hx, ?_⟩
    show r * u.val ≤ c (r • x)
    rw [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hu hr

/-- A set that is enclosed carries none of the enclosure's bounds: `{0}` is
bounded along `id` and the line containing it is not. Why no operation class
composes a bound — each guarantees only that the computed set is the larger. -/
theorem exists_outer_without_supportBound :
    ∃ X Y : Set ℝ, X ⊆ Y ∧ Nonempty (SupportBound X LinearMap.id) ∧
      IsEmpty (SupportBound Y LinearMap.id) := by -- --- PROOF ---
  refine ⟨{0}, Set.univ, Set.subset_univ _, ⟨⟨0, ?_⟩⟩, ⟨fun u => ?_⟩⟩
  · intro x hx
    exact le_of_eq hx
  · have h := u.le (u.val + 1) (Set.mem_univ _)
    simp only [LinearMap.id_coe, id_eq] at h
    linarith

/-- The sublevel set of a linear functional, which is the halfspace a bound
names. -/
theorem convex_le (c : α →ₗ[ℝ] ℝ) (v : ℝ) : Convex ℝ {w : α | c w ≤ v} := by -- --- PROOF ---
  intro p hp q hq a b ha hb hab
  show c (a • p + b • q) ≤ v
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc a * c p + b * c q ≤ a * v + b * v :=
        add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
    _ = v := by rw [← add_mul, hab, one_mul]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A halfspace is convex, so it holds the hull as soon as it holds the points.
This is what lets a convex hull be enclosed without ever forming it. -/
def SupportBound.convexHull (u : SupportBound S c) : SupportBound (convexHull ℝ S) c where
  val := u.val
  le _ hx := convexHull_min (fun y hy => u.le y hy) (convex_le c u.val) hx

/-- Immediate from `mono` and `subset_convexHull`: the point already witnesses
`S`, and `S` sits inside its own hull. -/
def SupportWitness.convexHull (u : SupportWitness S c) : SupportWitness (convexHull ℝ S) c :=
  u.mono (subset_convexHull ℝ S)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
