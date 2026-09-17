import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.reindex` over a floating-point scalar

Both bounds relabelled, and nothing rounds: a permutation moves stored floats
without arithmetic, so this is the exact layer's operation with the scalar
swapped and no error to pay.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.reindex (e : Fin m ≃ Fin n) (I : Interval 𝕋 n) : Interval 𝕋 m where
  inf := fun i => I.inf (e i)
  sup := fun i => I.sup (e i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
