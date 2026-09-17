import CORALean.ContSet.Interval.Float.Operations.Reindex
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.reindex` over a floating-point scalar

Centre, generator rows and error box all relabelled, and nothing rounds: a
permutation moves stored floats without arithmetic. The generator index is
untouched — only the coordinate axis moves, which is why the row index alone
carries `e`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.reindex (e : Fin m ≃ Fin n) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m where
  h := Z.h
  c := fun i => Z.c (e i)
  G := fun i j => Z.G (e i) j
  E := Z.E.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
