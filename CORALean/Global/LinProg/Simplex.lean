import CORALean.Global.Mathlib

/-!
# A simplex, deliberately outside the trusted base

`Duality` turns a nonnegative weighting of the rows into a bound. Something has
to produce the weighting, and this is it: a two-phase tableau simplex over any
ordered field, with no proof attached to any part of it.

Nothing downstream trusts what comes out. The caller checks nonnegativity and
dual feasibility itself and builds the `SupportBound` out of that check, so a
pivoting bug, an exhausted budget or a degenerate cycle costs a bound or its
tightness and can never cost soundness.

Iteration is bounded by `fuel` rather than by a termination argument, which is
what keeps every definition here structurally recursive and total.

What is solved is the *dual* of `max cᵀx` over `A x ≤ b`, namely `min bᵀy` over
`Aᵀ y = c, y ≥ 0`: phase one prices the artificial columns out, phase two
minimises `bᵀy`, and a candidate comes back as soon as phase one succeeds.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕂 : Type} [Field 𝕂] [LinearOrder 𝕂]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A tableau entry, out of range reading as zero, so every loop below indexes
by `ℕ` and none of them carries a range proof. -/
def aux_entry (T : Array (Array 𝕂)) (i j : ℕ) : 𝕂 := (T.getD i #[]).getD j 0

/-- Row `r` scaled to a unit pivot in column `q`, that column then eliminated
from every other row, the objective row included. -/
def aux_pivot (T : Array (Array 𝕂)) (r q : ℕ) : Array (Array 𝕂) :=
  let piv := (T.getD r #[]).map (· / aux_entry T r q)
  T.mapIdx fun i row =>
    if i = r then piv else row.mapIdx fun j a => a - row.getD q 0 * piv.getD j 0

/-- Bland's entering column: the first improving one, which is what keeps the
loop from cycling without anything proving that it does not. -/
def aux_enter (T : Array (Array 𝕂)) (obj lim : ℕ) : Option ℕ :=
  (List.range lim).find? fun q => if aux_entry T obj q < 0 then true else false

/-- The ratio test, ties broken by the smaller basic index — Bland again. -/
def aux_leave (T : Array (Array 𝕂)) (basis : Array ℕ) (rhs q rows : ℕ) : Option ℕ :=
  Prod.fst <$> (List.range rows).foldl (fun best r =>
    let a := aux_entry T r q
    if a ≤ 0 then best else
      let t := aux_entry T r rhs / a
      match best with
      | none => some (r, t)
      | some (r', t') =>
        if t < t' ∨ (t = t' ∧ basis.getD r 0 < basis.getD r' 0) then some (r, t) else best)
    (none : Option (ℕ × 𝕂))

/-- One pivot per unit of fuel. Exhaustion, optimality and an unbounded
objective all just stop, and the caller reads the tableau to tell them apart. -/
def aux_run (fuel : ℕ) (T : Array (Array 𝕂)) (basis : Array ℕ) (obj rhs rows lim : ℕ) :
    Array (Array 𝕂) × Array ℕ :=
  match fuel with
  | 0 => (T, basis)
  | f + 1 =>
    match aux_enter T obj lim with
    | none => (T, basis)
    | some q =>
      match aux_leave T basis rhs q rows with
      | none => (T, basis)
      | some r => aux_run f (aux_pivot T r q) (basis.set! r q) obj rhs rows lim

/-- The reduced costs of `cost` at the current basis, which is the objective row
a phase starts from. `cost` is read at the right-hand side column too, where
every cost vector here is zero. -/
def aux_costRow (T : Array (Array 𝕂)) (basis : Array ℕ) (cost : ℕ → 𝕂) (rows cols : ℕ) :
    Array 𝕂 :=
  (List.range cols).toArray.map fun j =>
    cost j - (List.range rows).foldl (fun s r => s + cost (basis.getD r 0) * aux_entry T r j) 0

/-- Artificials left basic at zero, pivoted out wherever a real column can take
their place. A row with no such column is redundant, and the artificial sitting
in it can no longer move, which is what lets phase two ignore them. -/
def aux_expel (T : Array (Array 𝕂)) (basis : Array ℕ) (lim rows : ℕ) :
    Array (Array 𝕂) × Array ℕ :=
  (List.range rows).foldl (fun st r =>
    if st.2.getD r 0 < lim then st
    else
      match (List.range lim).find? fun q => if aux_entry st.1 r q = 0 then false else true with
      | none => st
      | some q => (aux_pivot st.1 r q, st.2.set! r q)) (T, basis)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A dual candidate for `max cᵀx` over `A x ≤ b`: weights that *should* be
nonnegative and *should* satisfy `Aᵀ y = c`. Nothing here says that they are. -/
def dualCandidate (fuel : ℕ) {m n : ℕ} (A : Fin m → Fin n → 𝕂) (b : Fin m → 𝕂)
    (c : Fin n → 𝕂) : Option (Fin m → 𝕂) :=
  let AN : ℕ → ℕ → 𝕂 := fun i j =>
    if hi : i < m then (if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0
  let cN : ℕ → 𝕂 := fun j => if h : j < n then c ⟨j, h⟩ else 0
  let rhs := m + n
  let cols := rhs + 1
  -- one signed row per primal variable, with an artificial column of its own
  let T₀ : Array (Array 𝕂) := (List.range n).toArray.map fun j =>
    let s : 𝕂 := if cN j < 0 then -1 else 1
    (List.range cols).toArray.map fun k =>
      if k = rhs then s * cN j
      else if k < m then s * AN k j
      else if k = m + j then 1 else 0
  let basis₀ : Array ℕ := (List.range n).toArray.map (m + ·)
  -- phase one, over every column: the artificials go to zero or the dual is infeasible
  let obj₁ := aux_costRow T₀ basis₀ (fun k => if m ≤ k ∧ k < rhs then 1 else 0) n cols
  let (T₁, basis₁) := aux_run fuel (T₀.push obj₁) basis₀ n rhs n rhs
  -- the objective row's right-hand side is the negated phase-one optimum
  if aux_entry T₁ n rhs < 0 then none
  else
    let (T₂, basis₂) := aux_expel T₁ basis₁ m n
    -- phase two, over the real columns alone, minimising the bound `bᵀy` itself
    let obj₂ := aux_costRow T₂ basis₂ (fun k => if h : k < m then b ⟨k, h⟩ else 0) n cols
    let (T₃, basis₃) := aux_run fuel (T₂.set! n obj₂) basis₂ n rhs n m
    -- a variable's value is its basic row's right-hand side, and zero otherwise
    some fun i =>
      match (List.range n).find? fun r => if basis₃.getD r 0 = (i : ℕ) then true else false with
      | none => 0
      | some r => aux_entry T₃ r rhs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
