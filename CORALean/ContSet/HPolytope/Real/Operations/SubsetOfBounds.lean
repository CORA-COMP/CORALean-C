import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

/-!
# `HPolytope.ofBounds` encloses

Nothing here solves a linear program. It consumes the answers.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {S : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.subset_ofBounds (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u : ∀ i, SupportBound S (Aq i)) : S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun _ hx => ⟨fun i => (u i).le _ hx, fun i => i.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
