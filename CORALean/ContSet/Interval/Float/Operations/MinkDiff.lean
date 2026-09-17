import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.minkDiff`

A difference is a guarantee, so `MinkDiff` owes an **inner** approximation: the
computed set may only ever be a subset of the true difference. Rounding the
lower bound *up* and the upper bound *down* shrinks the box, which is the
direction that keeps it inside. Every other float operation here widens; this
one narrows, and a reader who pattern-matches on `addDown`/`addUp` will get it
backwards.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.minkDiff (I₁ I₂ : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i => subUp (I₁.inf i) (I₂.inf i)
  sup := fun i => subDown (I₁.sup i) (I₂.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
