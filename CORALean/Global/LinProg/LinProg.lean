import CORALean.Global.Tensor

/-!
# Bounds on a linear objective

Every operation that has to leave one set representation for another eventually
asks the same question: how far does this set reach in direction `c`? For a
polytope that question is a linear program, and this is the shape of its answer.

A `SupportBound` is a number together with the fact that no point of the set
exceeds it. It says nothing about where the number came from, which is exactly
the point: a simplex implementation may produce it and need not be trusted,
because the dual solution it returns *proves* the bound by weak duality, and it
is the proof that gets carried. Nothing here is axiomatised and nothing is
`sorry`; an unverified solver stays outside the trusted base by construction.

Stated over a `Set`, not a representation, so a bound transfers along the set
operations rather than along any particular description of them —
`Duality` says where bounds come from, `Composition` how they travel.

`SupportWitness` is the dual: a value with a point attaining it; no `ofEmpty`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   15-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S T : Set α} {c : α →ₗ[ℝ] ℝ}


-- ========================================  MAIN TYPE  ========================================= --

structure SupportBound (S : Set α) (c : α →ₗ[ℝ] ℝ) where
  val : ℝ
  le : ∀ x ∈ S, c x ≤ val

/-- A bound on the larger set bounds the smaller. -/
def SupportBound.mono (h : S ⊆ T) (u : SupportBound T c) : SupportBound S c :=
  ⟨u.val, fun x hx => u.le x (h hx)⟩

/-- A bound may always be loosened, which is what makes rounding it outward
sound. -/
def SupportBound.raise (u : SupportBound S c) {v : ℝ} (h : u.val ≤ v) : SupportBound S c :=
  ⟨v, fun x hx => le_trans (u.le x hx) h⟩

/-- Nothing to exceed, so any number will do. -/
def SupportBound.ofEmpty (v : ℝ) : SupportBound (∅ : Set α) c :=
  ⟨v, fun _ h => h.elim⟩

structure SupportWitness (S : Set α) (c : α →ₗ[ℝ] ℝ) where
  val : ℝ
  mem : ∃ x ∈ S, val ≤ c x

/-- A witness for `S` is a witness for any larger set — the opposite direction
from `SupportBound.mono`. -/
def SupportWitness.mono (h : S ⊆ T) (u : SupportWitness S c) : SupportWitness T c :=
  ⟨u.val, let ⟨x, hx, hv⟩ := u.mem; ⟨x, h hx, hv⟩⟩

/-- A witness may always be weakened downward, which is what makes rounding it
inward sound. -/
def SupportWitness.lower (u : SupportWitness S c) {v : ℝ} (h : v ≤ u.val) : SupportWitness S c :=
  ⟨v, let ⟨x, hx, hv⟩ := u.mem; ⟨x, hx, le_trans h hv⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
