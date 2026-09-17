import CORALean.Global.Mathlib

/-!
# Splitting an index type into parts

`Split α into β` names every index of `α` exactly once as `P.on k l`, where `k`
picks a part and `l` an index within it. Two parts are the common case and read
`Split α into βₗ ⊕ βᵣ`, with `P.left` and `P.right`.

`sum_split` is why the type exists: a sum over `α` splits along the parts with
no side condition, since the equivalence already rules out overlap.

The type is `Partition`; `Split` is only its notation, since naming the two
alike would make `Partition` a keyword. `ofPred` builds one out of a decidable
predicate, for a caller that only has one of those, such as a merge bucket.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

universe v


-- ========================================  MAIN TYPE  ========================================= --

structure Partition (α : Type*) {κ : Type*} (β : κ → Type*) where
  index : (Σ k, β k) ≃ α

/-- The two-part family. -/
def Pair (β γ : Type v) : Bool → Type v
  | true => β
  | false => γ

/-- Two parts, the common case. -/
abbrev Partition₂ (α : Type*) (β γ : Type v) := Partition α (Pair β γ)

scoped notation:50 "Split " α:max " into " β:max => CORALean.Partition α β
scoped notation:50 "Split " α:max " into " β:max " ⊕ " γ:max => CORALean.Partition₂ α β γ

instance {β γ : Type v} [Fintype β] [Fintype γ] : (b : Bool) → Fintype (Pair β γ b)
  | true => inferInstanceAs (Fintype β)
  | false => inferInstanceAs (Fintype γ)

variable {α α' κ M : Type*} {β : κ → Type*} {βₗ βᵣ : Type v}

def Pair.equivSum (β γ : Type v) : (Σ b, Pair β γ b) ≃ β ⊕ γ where
  toFun := fun ⟨b, x⟩ => match b, x with
    | true, x => Sum.inl x
    | false, x => Sum.inr x
  invFun := fun s => match s with
    | Sum.inl x => ⟨true, x⟩
    | Sum.inr x => ⟨false, x⟩
  left_inv := by rintro ⟨(_ | _), x⟩ <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- Split at `q`, first part first: `left` is `Fin.castAdd` and `right` is
`Fin.natAdd`, both by `rfl`. -/
def Partition.split (q r : ℕ) : Split (Fin (q + r)) into (Fin q) ⊕ (Fin r) where
  index := (Pair.equivSum (Fin q) (Fin r)).trans finSumFinEquiv

/-- Rename what a partition splits: every selection rule is `split` composed with
the permutation that orders the indices. -/
def Partition.reindex (P : Split α into βₗ ⊕ βᵣ) (e : α' ≃ α) : Split α' into βₗ ⊕ βᵣ where
  index := P.index.trans e.symm

/-- The split a decidable predicate cuts `Fin n` into: the neurons failing `p`
survive on the left, those satisfying it are the bucket on the right. Built from
`Fintype.equivFin` on each subtype, `Equiv.sumCompl` for the swap and `p`. -/
noncomputable def Partition.ofPred {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Split (Fin n) into (Fin (Fintype.card {i : Fin n // ¬ p i}))
      ⊕ (Fin (Fintype.card {i : Fin n // p i})) where
  index := ((Pair.equivSum _ _).trans
      (Equiv.sumCongr (Fintype.equivFin {i : Fin n // ¬ p i}).symm
        (Fintype.equivFin {i : Fin n // p i}).symm)).trans
    ((Equiv.sumComm {i : Fin n // ¬ p i} {i : Fin n // p i}).trans (Equiv.sumCompl p))

def Partition.on (P : Split α into β) (k : κ) (l : β k) : α := P.index ⟨k, l⟩

def Partition.left (P : Split α into βₗ ⊕ βᵣ) (l : βₗ) : α := P.on true l

def Partition.right (P : Split α into βₗ ⊕ βᵣ) (l : βᵣ) : α := P.on false l

/-- Every bucket index satisfies the predicate it was cut out by. -/
theorem Partition.ofPred_right {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (l : Fin (Fintype.card {i : Fin n // p i})) :
    p ((Partition.ofPred p).right l) :=
  ((Fintype.equivFin {i : Fin n // p i}).symm l).property

/-- Every surviving index fails the predicate that cut out the bucket. -/
theorem Partition.ofPred_left {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (l : Fin (Fintype.card {i : Fin n // ¬ p i})) :
    ¬ p ((Partition.ofPred p).left l) :=
  ((Fintype.equivFin {i : Fin n // ¬ p i}).symm l).property

theorem Partition.sum_split [AddCommMonoid M] [Fintype α] [Fintype κ] [∀ k, Fintype (β k)]
    (P : Split α into β) (f : α → M) :
    ∑ j, f j = ∑ k, ∑ l, f (P.on k l) := by
  rw [← Equiv.sum_comp P.index f, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

theorem Partition.sum_split₂ [AddCommMonoid M] [Fintype α] [Fintype βₗ] [Fintype βᵣ]
    (P : Split α into βₗ ⊕ βᵣ) (f : α → M) :
    ∑ j, f j = ∑ l, f (P.left l) + ∑ l, f (P.right l) := by
  rw [P.sum_split f, Fintype.sum_bool]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
