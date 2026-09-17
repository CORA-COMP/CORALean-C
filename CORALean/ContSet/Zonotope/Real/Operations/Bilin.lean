import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.bilin`

Any bilinear map applied to two zonotopes over *different* ambient types, each
kept in its own module. With `A = c₁ + Σᵢ αᵢ • g₁ᵢ` and `x = c₂ + Σⱼ βⱼ • g₂ⱼ`,

    f A x = f c₁ c₂ + Σᵢ αᵢ f(g₁ᵢ, c₂) + Σⱼ βⱼ f(c₁, g₂ⱼ) + Σᵢⱼ αᵢβⱼ f(g₁ᵢ, g₂ⱼ)

which is the centre and the three generator blocks below, the cross block
flattened by `finProdFinEquiv`. Unlike `PolyZonotope.bilin`, there is nowhere
here to record that a cross coefficient really is `αᵢβⱼ`: a zonotope's
coefficients are free in `[-1, 1]`, so the cross block only over-approximates —
see `bilin_outer`. There is therefore no `bilin_exact` counterpart.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.bilin (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (Z₁ : Zonotope α) (Z₂ : Zonotope β) : Zonotope γ where
  h := Z₁.h + Z₂.h + Z₁.h * Z₂.h
  c := f Z₁.c Z₂.c
  G := Fin.append (Fin.append (fun i => f (Z₁.G i) Z₂.c) (fun j => f Z₁.c (Z₂.G j)))
        (fun k => f (Z₁.G (finProdFinEquiv.symm k).1) (Z₂.G (finProdFinEquiv.symm k).2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
