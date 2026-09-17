import CORALean.Global.Mathlib

/-!
# Ordering indices by a comparator

`sortPerm` is `mergeSort` read back as a permutation: it names the indices in
the order a comparator puts them.

The comparator is asked for nothing — not transitivity, not totality. That is
what makes this usable where `Tuple.sort` is not: `Tuple.sort` needs a
`LinearOrder`, and a floating-point scalar cannot lawfully have one, since
distinct representations of the same value compare equal in both directions.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sortPerm r k` is the index `mergeSort` places at rank `k`. -/
def sortPerm {n : ℕ} (r : Fin n → Fin n → Bool) : Equiv.Perm (Fin n) :=
  let l := (List.finRange n).mergeSort r
  have hperm : l.Perm (List.finRange n) := List.mergeSort_perm _ _
  have hlen : n = l.length := by rw [hperm.length_eq, List.length_finRange]
  (finCongr hlen).trans
    (((List.nodup_finRange n).perm hperm.symm).getEquivOfForallMemList l
      fun x => hperm.mem_iff.mpr (List.mem_finRange x))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
