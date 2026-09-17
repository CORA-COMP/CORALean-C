import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffOrEmpty
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner

/-!
# `Zonotope.minkDiffOrEmpty` is an inner approximation of the Minkowski difference

Stated at the zonotope the wrapper returns rather than at the wrapper itself,
which keeps this file clear of the `ContSet` instance: that lives in
`Instances.lean`, which imports this one. The empty case needs no statement —
`∅` is inside every difference — so the hypothesis is what carries the content.

`h.choose` is the certified representation the definition picked, and
`Option.some_get` turns the `isSome` that came with it back into the equation
`minkDiffRep_inner` asks for.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffOrEmpty_inner (Z₁ Z₂ : Zonotope α) {D : Zonotope α}
    (hD : Z₁.minkDiffOrEmpty Z₂ = .of D) :
    D.construct ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  unfold Zonotope.minkDiffOrEmpty at hD
  split_ifs at hD with h
  -- `D` is what the chosen candidate returned, and that candidate checked out
  obtain rfl : (Z₁.minkDiffRep Z₂ h.choose).get h.choose_spec = D := WithEmpty.of.inj hD
  exact Zonotope.minkDiffRep_inner Z₁ Z₂ h.choose (Option.some_get h.choose_spec).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
