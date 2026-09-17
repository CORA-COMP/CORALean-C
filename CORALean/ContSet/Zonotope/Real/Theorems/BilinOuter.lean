import CORALean.ContSet.Zonotope.Real.Operations.Bilin

/-!
# `bilin` over-approximates `f` applied across the two zonotopes

The witness pairs each admissible coefficient of `Z₁` with each of `Z₂`:
`Fin.append (Fin.append p q) (fun k => p _ * q _)` at the same index split as
`bilin`'s generators. Each cross coefficient is bounded by `abs_mul` and
`mul_le_one₀`, but taken free rather than tied to `p` and `q` — the
enlargement that keeps this an enclosure and not an equality, unlike
`PolyZonotope.bilin`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The combinatorics behind splitting a sum over `bilin`'s generator count: two
applications of `Fin.sum_univ_add`, the cross block reindexed to a pair through
`finProdFinEquiv`. -/
theorem Zonotope.aux_sum_univ_add3 {δ : Type} [AddCommMonoid δ] {m n : ℕ}
    (g : Fin (m + n + m * n) → δ) :
    ∑ k, g k = ∑ i, g (Fin.castAdd (m * n) (Fin.castAdd n i))
      + ∑ j, g (Fin.castAdd (m * n) (Fin.natAdd m j))
      + ∑ i, ∑ j, g (Fin.natAdd (m + n) (finProdFinEquiv (i, j))) := by -- --- PROOF ---
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hpair : ∑ p : Fin m × Fin n, g (Fin.natAdd (m + n) (finProdFinEquiv p))
      = ∑ i, g (Fin.natAdd (m + n) i) :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  rw [← hpair, Fintype.sum_prod_type]

/-- The same split, read through `bilin`'s own generator count, stated at the
projection because that is the form `rw` meets in the goal below. -/
theorem Zonotope.aux_sum_univ_bilin (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (Z₁ : Zonotope α) (Z₂ : Zonotope β)
    {δ : Type} [AddCommMonoid δ] (g : Fin (Zonotope.bilin f Z₁ Z₂).h → δ) :
    ∑ k, g k = ∑ i, g (Fin.castAdd (Z₁.h * Z₂.h) (Fin.castAdd Z₂.h i))
      + ∑ j, g (Fin.castAdd (Z₁.h * Z₂.h) (Fin.natAdd Z₁.h j))
      + ∑ i, ∑ j, g (Fin.natAdd (Z₁.h + Z₂.h) (finProdFinEquiv (i, j))) :=
  Zonotope.aux_sum_univ_add3 g

/-- `f` applied at a fixed second point distributes over a centre-plus-generators
sum in the first argument. -/
theorem Zonotope.aux_bilin_left (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) {h : ℕ} (c : α) (G : Fin h → α)
    (p : Fin h → ℝ) (x : β) : f (c + ∑ i, p i • G i) x = f c x + ∑ i, p i • f (G i) x := by
  rw [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply])

/-- Any linear map distributes over a centre-plus-generators sum. -/
theorem Zonotope.aux_bilin_right (g : β →ₗ[ℝ] γ) {h : ℕ} (c : β) (G : Fin h → β)
    (q : Fin h → ℝ) : g (c + ∑ j, q j • G j) = g c + ∑ j, q j • g (G j) := by
  rw [map_add, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => map_smul g (q j) (G j))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.bilin_outer (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (Z₁ : Zonotope α) (Z₂ : Zonotope β) :
    (⋃ a ∈ Z₁.construct, (f a ·) '' Z₂.construct)
      ⊆ (Zonotope.bilin f Z₁ Z₂).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨a, ha, x, hx, rfl⟩ := hy
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hx
  refine ⟨Fin.append (Fin.append p q)
      (fun k => p (finProdFinEquiv.symm k).1 * q (finProdFinEquiv.symm k).2), ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simp only [Fin.append_left]
      exact Fin.addCases (fun i => by simpa using hp i) (fun j => by simpa using hq j) k
    · simp only [Fin.append_right, abs_mul]
      exact mul_le_one₀ (hp _) (abs_nonneg _) (hq _)
  · rw [Zonotope.aux_sum_univ_bilin f Z₁ Z₂]
    simp only [Zonotope.bilin, Fin.append_left, Fin.append_right]
    -- expand `f` bilinearly, generator block by generator block, then regroup
    rw [Zonotope.aux_bilin_left f Z₁.c Z₁.G p _, Zonotope.aux_bilin_right (f Z₁.c) Z₂.c Z₂.G q]
    have hcross : ∀ i, p i • f (Z₁.G i) (Z₂.c + ∑ j, q j • Z₂.G j)
        = p i • f (Z₁.G i) Z₂.c + ∑ j, (p i * q j) • f (Z₁.G i) (Z₂.G j) := by
      intro i
      rw [Zonotope.aux_bilin_right (f (Z₁.G i)) Z₂.c Z₂.G q, smul_add, Finset.smul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [smul_smul])
    simp only [hcross, Finset.sum_add_distrib, Equiv.symm_apply_apply]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
