import CORALean.ContSet.Zonotope.Real.Operations.Map

/-!
# `Zonotope.map` is exactly the image under a linear map

The same coefficients work in both directions — a linear map introduces no new
freedom and removes none — so linearity carried through the sum is the whole
proof. A linear image of a zonotope is a zonotope, which is what the propagation
loop rests on.

Every other image guarantee in this directory is this one at a particular linear
map. No `map_outer`: the float `map` pays its rounding into the error box, so it
reproves this alongside the spill rather than composing with it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.map_exact (f : α →ₗ[ℝ] β) (Z : Zonotope α) :
    f '' Z.construct = (Z.map f).construct := by -- --- PROOF ---
  have hf : ∀ b : Fin Z.h → ℝ, f (Z.c + ∑ j, b j • Z.G j)
      = (Z.map f).c + ∑ j, b j • (Z.map f).G j := by
    intro b
    rw [map_add, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => map_smul f (b j) (Z.G j))
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, hf b⟩
  · rintro y ⟨b, hb, hy⟩
    refine ⟨Z.c + ∑ j, b j • Z.G j, ⟨b, hb, rfl⟩, ?_⟩
    rw [hy]
    exact hf b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
