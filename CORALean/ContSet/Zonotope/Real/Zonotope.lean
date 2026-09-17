import CORALean.ContSet.Interval.Real.Interval

/-!
# Zonotopes: the representation

The matrix zonotope, `Zonotope (Mat ℝ m n)`, is [1, Eq. (8)].

CORA's `zonotope`, with the same centre `c` and generator matrix `G`, denoting
every point the generators reach from `c` with coefficients in `[-1, 1]`.

Over any real module, not just `Vec ℝ n`: nothing about a centre plus a bounded
combination of generators mentions coordinates. So `Zonotope (Mat ℝ n m)` is
CORA's `matZonotope` and needs no separate development.

Generators are a family rather than a matrix, a matrix being available only when
the ambient type has coordinates. At `Vec ℝ n` the two differ by transposition:
`G j i` is coordinate `i` of generator `j`.

The generator count is a field, not a type index: operations grow it freely and
`reduce` is what bounds it, where the algorithm asks rather than everywhere.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure Zonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α

def Zonotope.construct (Z : Zonotope α) : Set α :=
  {x | ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧ x = Z.c + ∑ j, β j • Z.G j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
