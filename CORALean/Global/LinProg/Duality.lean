import CORALean.Global.LinProg.LinProg

/-!
# Where a bound comes from: weak duality

Give the constraints nonnegative weights and add them up. Each inequality only
gets weaker when its left side is replaced by its right, and each equality does
not change at all, so whatever functional the weights assemble is bounded by
whatever number they assemble — for every feasible point at once, and with no
appeal to the existence of an optimum.

That is the whole trusted content of an LP bound. A solver's dual solution is
such a weighting, and a solver that returns a wrong one produces no bound rather
than a wrong one.

Setting the objective to zero turns the same statement into a certificate of
infeasibility, so the empty case needs nothing new.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {m me : ℕ}

/-- The feasible set of `A x ≤ b`, `Ae x = be`, written out rather than named:
`Global` sees no set representations, and a halfspace description unfolds to
this. -/
def Feasible (A : Fin m → (α →ₗ[ℝ] ℝ)) (b : Fin m → ℝ)
    (Ae : Fin me → (α →ₗ[ℝ] ℝ)) (be : Fin me → ℝ) : Set α :=
  {x | (∀ i, A i x ≤ b i) ∧ ∀ i, Ae i x = be i}

theorem le_dual_bound (A : Fin m → (α →ₗ[ℝ] ℝ)) (b : Fin m → ℝ)
    (Ae : Fin me → (α →ₗ[ℝ] ℝ)) (be : Fin me → ℝ)
    (y : Fin m → ℝ) (z : Fin me → ℝ) (hy : ∀ i, 0 ≤ y i)
    {x : α} (hle : ∀ i, A i x ≤ b i) (heq : ∀ i, Ae i x = be i) :
    (∑ i, y i * A i x) + (∑ i, z i * Ae i x) ≤ (∑ i, y i * b i) + ∑ i, z i * be i := by
  refine add_le_add (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hy i)) ?_
  exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [heq i])

/-- The dual solution `(y, z)` bounds every objective it assembles. The
hypothesis is the dual feasibility `c = yᵀA + zᵀAe`, stated pointwise because a
functional is determined by what it does. -/
def SupportBound.ofDual {A : Fin m → (α →ₗ[ℝ] ℝ)} {b : Fin m → ℝ}
    {Ae : Fin me → (α →ₗ[ℝ] ℝ)} {be : Fin me → ℝ} {c : α →ₗ[ℝ] ℝ}
    (y : Fin m → ℝ) (z : Fin me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hc : ∀ x : α, c x = (∑ i, y i * A i x) + ∑ i, z i * Ae i x) :
    SupportBound (Feasible A b Ae be) c where
  val := (∑ i, y i * b i) + ∑ i, z i * be i
  le x hx := by
    rw [hc x]
    exact le_dual_bound A b Ae be y z hy hx.1 hx.2


-- =======================================  MAIN THEOREM  ======================================= --

/-- Farkas: weights that cancel the objective but not the right-hand side leave
no feasible point at all. -/
theorem eq_empty_of_dual {A : Fin m → (α →ₗ[ℝ] ℝ)} {b : Fin m → ℝ}
    {Ae : Fin me → (α →ₗ[ℝ] ℝ)} {be : Fin me → ℝ}
    (y : Fin m → ℝ) (z : Fin me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (h0 : ∀ x : α, (∑ i, y i * A i x) + ∑ i, z i * Ae i x = 0)
    (hneg : (∑ i, y i * b i) + ∑ i, z i * be i < 0) :
    Feasible A b Ae be = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hle, heq⟩
  have h := le_dual_bound A b Ae be y z hy hle heq
  rw [h0 x] at h
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
