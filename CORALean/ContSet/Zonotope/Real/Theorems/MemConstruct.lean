import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Membership in a zonotope, coordinatewise

`construct` is stated over any real module, so its equation is between two
points of that module. At `Vec ℝ n` an operation reasons one coordinate at a
time instead, and this is the reading it uses: the same coefficients, the
generator entry transposed and the scalar on its right.

The float layer inherits it — its `mem_nominalSet_iff` is this theorem at the
nominal zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_construct_iff {n : ℕ} {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ Z.construct ↔
      ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = Z.c i + ∑ j,
        Z.G j i * β j := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, Entrywise.add_sum_smul_apply Z.c Z.G β⟩
  -- back, the pointwise equalities collected into one by `funext`
  · rintro ⟨β, hβ, hx⟩
    exact ⟨β, hβ, funext fun i => (hx i).trans (Entrywise.add_sum_smul_apply Z.c Z.G β i).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
