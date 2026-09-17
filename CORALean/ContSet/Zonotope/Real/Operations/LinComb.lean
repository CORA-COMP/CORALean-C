import CORALean.ContSet.Zonotope.Real.Operations.PairDiff
import CORALean.ContSet.Zonotope.Real.Operations.PairSum
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Zonotopes: the linear combination of two

CORA's `@zonotope/enclose`, which is where a zonotope's `linComb` comes from.
The centre is the midpoint, one fresh generator spans the half-difference of the
centres — which is what lets the combination slide from one set to the other —
and the two generator blocks are paired column by column, by `pairSum` and
`pairDiff`, the longer block keeping its surplus at full width.

Pairing is what makes this tighter than concatenating the blocks, at the same
count `h₁ + h₂ + 1`. Over a paired column the result reaches
`{u G₁ⱼ + v G₂ⱼ | |u| + |v| ≤ 1}`, the hull of `±G₁ⱼ` and `±G₂ⱼ`, rather than
the whole box: the coefficients come out as `λ β₁ⱼ ± (1-λ) β₂ⱼ`, which records
that the two sides share one `λ`.

The columns come out as `sum ++ difference ++ centre` rather than CORA's
`sum ++ centre ++ difference ++ surplus`; a zonotope does not depend on the
order of its generators.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.linComb (Z₁ Z₂ : Zonotope α) : Zonotope α where
  h := Z₁.h + Z₂.h + 1
  c := (2:ℝ)⁻¹ • (Z₁.c + Z₂.c)
  G := Fin.append (Fin.append (Zonotope.pairSum Z₁.G Z₂.G) (Zonotope.pairDiff Z₁.G Z₂.G))
        (fun _ : Fin 1 => (2:ℝ)⁻¹ • (Z₁.c - Z₂.c))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
