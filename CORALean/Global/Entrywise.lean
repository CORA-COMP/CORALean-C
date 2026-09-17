import CORALean.Global.Tensor

/-!
# Ambient types that have coordinates

Which ambient types can be read coordinate by coordinate, and what an index then
is: `Fin n` for a vector, `Fin m × Fin n` for a matrix. An axis-aligned box, a
generator ranking and an entrywise bound all need this.

`entry` is linear and injective, which is what makes an entrywise definition the
operation on the space itself rather than merely one that agrees with it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

class Entrywise (α : Type) (ι : outParam Type) [AddCommGroup α] [Module ℝ α] where
  entry : α → ι → ℝ
  /-- The point with the given coordinates; `Interval.linComb` builds bounds
  this way. -/
  ofEntry : (ι → ℝ) → α
  entry_ofEntry (f : ι → ℝ) (i : ι) : entry (ofEntry f) i = f i
  ofEntry_entry (a : α) : ofEntry (entry a) = a
  entry_add (a b : α) (i : ι) : entry (a + b) i = entry a i + entry b i
  entry_smul (c : ℝ) (a : α) (i : ι) : entry (c • a) i = c * entry a i

namespace Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

attribute [simp] entry_ofEntry

/-- `ofEntry` inverts `entry`, so coordinates determine the point. -/
theorem entry_injective : Function.Injective (entry : α → ι → ℝ) := by
  intro a b h
  rw [← ofEntry_entry a, ← ofEntry_entry b, h]

@[simp] theorem entry_zero (i : ι) : entry (0 : α) i = 0 := by
  have h := entry_add (0 : α) 0 i
  rw [add_zero] at h
  linarith

/-- The additive structure is read coordinatewise, so negation is too. -/
@[simp] theorem entry_neg (a : α) (i : ι) : entry (-a) i = -entry a i := by
  have h := entry_add a (-a) i
  rw [add_neg_cancel, entry_zero] at h
  linarith

theorem entry_sub (a b : α) (i : ι) : entry (a - b) i = entry a i - entry b i := by
  rw [sub_eq_add_neg, entry_add, entry_neg, sub_eq_add_neg]

theorem ext {a b : α} (h : ∀ i, entry a i = entry b i) : a = b :=
  entry_injective (funext h)

/-- Reading one coordinate, bundled, which is what lets it pass a sum. -/
def entryHom (i : ι) : α →+ ℝ where
  toFun a := entry a i
  map_zero' := entry_zero i
  map_add' a b := entry_add a b i

theorem entry_sum {κ : Type} (s : Finset κ) (f : κ → α) (i : ι) :
    entry (∑ x ∈ s, f x) i = ∑ x ∈ s, entry (f x) i :=
  map_sum (entryHom i) f s

/-- A point is the sum of its coordinates against the standard basis. Compares
entries: `entry` of the right side at `j` collapses the sum to `entry x j`,
and `entry_injective` finishes it. -/
theorem eq_sum_single [Fintype ι] [DecidableEq ι] (x : α) :
    x = ∑ i, entry x i • ofEntry (Pi.single i 1) := by
  refine ext fun j => ?_
  rw [entry_sum]
  simp [entry_smul, Pi.single_apply]

/-- A centre plus a scaled family, read coordinatewise, with the scalar on the
right — the form every generator-based representation states its membership in.
Shared so that each of them states it once. -/
theorem entry_add_sum_smul {m : ℕ} (c : α) (G : Fin m → α) (β : Fin m → ℝ) (i : ι) :
    entry (c + ∑ j, β j • G j) i = entry c i + ∑ j, entry (G j) i * β j := by
  rw [entry_add, entry_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [entry_smul, mul_comm])

end Entrywise

/-- A vector is its own coordinates. -/
instance {n : ℕ} : Entrywise (Vec ℝ n) (Fin n) where
  entry v i := v i
  ofEntry f := f
  entry_ofEntry _ _ := rfl
  ofEntry_entry _ := rfl
  entry_add _ _ _ := rfl
  entry_smul _ _ _ := rfl

/-- True by `rfl`, but a proof stated in coordinates has to rewrite with it. -/
@[simp] theorem Entrywise.entry_vec {n : ℕ} (v : Vec ℝ n) (i : Fin n) :
    Entrywise.entry v i = v i := rfl

/-- Indexed by a pair. `Mat` is its own type former, not `Tensor`, so this does
not collide with the vector instance. -/
instance {m n : ℕ} : Entrywise (Mat ℝ m n) (Fin m × Fin n) where
  entry A p := A p.1 p.2
  ofEntry f := fun i j => f (i, j)
  entry_ofEntry _ _ := rfl
  ofEntry_entry _ := rfl
  entry_add _ _ _ := rfl
  entry_smul _ _ _ := rfl

@[simp] theorem Entrywise.entry_mat {m n : ℕ} (A : Mat ℝ m n) (p : Fin m × Fin n) :
    Entrywise.entry A p = A p.1 p.2 := rfl

/-- `entry_add_sum_smul` at `Vec`, where a coordinate is an application. This is
the spelling a generator-based representation states `mem_construct_iff` in, so
it is stated once here rather than per representation. -/
theorem Entrywise.add_sum_smul_apply {n m : ℕ} (c : Vec ℝ n) (G : Fin m → Vec ℝ n)
    (β : Fin m → ℝ) (i : Fin n) : (c + ∑ j, β j • G j) i = c i + ∑ j, G j i * β j :=
  Entrywise.entry_add_sum_smul c G β i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
