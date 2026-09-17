import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Zonotope.Real.Operations.RadiusReach

/-!
# Zonotopes: multiplication by an interval matrix

CORA writes this as `mtimes` too, dispatching on the argument. The centre acts
exactly, as a matrix does, and everything the radius allows is boxed into one
fresh generator per coordinate — so a step costs `n` generators and no more.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.mtimesIntervalMat (IM : Interval (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := Z.h + m
  c := IM.center *ᵥ Z.c
  G := Fin.append (fun l => IM.center *ᵥ Z.G l)
        (Matrix.diagonal fun i => Zonotope.radiusReach IM Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
