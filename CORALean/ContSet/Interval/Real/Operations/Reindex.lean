import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.reindex`

Both bounds relabelled by the same permutation, which is all a box has to say
about a change of coordinate order.

At `Vec ℝ n` rather than at every ambient type with coordinates: the index type
is what moves, and a permutation of an arbitrary `ι` would need the ambient type
to be indexed by it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.reindex (e : Fin m ≃ Fin n) (I : Interval (Vec ℝ n)) : Interval (Vec ℝ m) where
  inf := reindexLin e I.inf
  sup := reindexLin e I.sup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
