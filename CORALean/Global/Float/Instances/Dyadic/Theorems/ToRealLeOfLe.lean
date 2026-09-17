import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff

/-!
# `le` only approves what is true

The direction `SoundFloatArithmetic` asks for; the converse holds too
(`le_iff`), but nothing here needs it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The direction `SoundFloatArithmetic` asks for; the converse holds too
(`le_iff`), but nothing here needs it. -/
theorem toReal_le_of_le {a b : Dyadic p} (h : le a b = true) : toReal a ≤ toReal b :=
  (le_iff a b).mp h

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
