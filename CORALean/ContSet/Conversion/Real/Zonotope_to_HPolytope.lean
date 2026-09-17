import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBounds

/-!
# A zonotope as halfspaces

`Zonotope.supportBound` answers a direction without a linear program, exactly,
at one dot product per generator — which is why it is where the two
representations meet.

The rows are the caller's, as always. Exact when they are the zonotope's own
facet normals, of which there are `2·C(h, n-1)` — the reason CORA does not
convert a zonotope to halfspaces unless it has to.

`supportBound` is the `d̃` of [1, Prop. 4], where a halfspace description
absorbs a zonotope without enumerating either one's vertices.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation".
      arXiv:2310.19083, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

def Zonotope.hPolytope (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => Z.supportBound (Aq i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.hPolytope_contains (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    Z.construct ⊆ (Z.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
