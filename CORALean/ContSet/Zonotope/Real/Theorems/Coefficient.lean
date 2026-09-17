import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The coefficient that hits a target with one symmetric generator

A generator of radius `R` reaches exactly `[-R, R]`, so any `D` with `|D| ≤ R`
is `R * coefficient R D`. The `R = 0` branch is what makes this total: there the
bound pins `D` to zero, so any coefficient does and `0` is picked.

A proof device rather than an operation, hence in `Theorems/` and not in
`Operations/`: it only ever witnesses an existential and is never run.
`AbsCoefficientLeOne` and `MulCoefficient` are the two facts about it, and
`reduce` and the float `absorbError` are what need them.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.coefficient (R D : ℝ) : ℝ := if R = 0 then 0 else D / R

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
