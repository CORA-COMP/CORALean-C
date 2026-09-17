import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# What storing a midpoint leaves to pay

The two directed midpoints bracket the exact one, halving being exact, so the
gap between the stored value and the exact one is what `midpointResidual`
records. Every operation whose centre is a midpoint owes this, which is why it
is stated once rather than inside one of them.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.midpoint_mem_residual (a b : Vec 𝕋 n) :
    (fun i => (toReal (a i) + toReal (b i)) / 2 - toReal (Zonotope.midpoint a b i))
      ∈ (Zonotope.midpointResidual a b).construct :=
  Interval.sub_mem_residual fun i => by
    refine ⟨?_, ?_⟩
    · rw [toReal_half]
      have := addDown_le_add (a i) (b i)
      linarith
    · rw [toReal_half]
      have := add_le_addUp (a i) (b i)
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
