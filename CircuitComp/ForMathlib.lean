import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.Partrec
import Mathlib.Computability.Ackermann
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Floor

import Mathlib.Tactic.Peel
import Mathlib.Tactic.Bound

--PULLOUT, mathlibable
theorem Finset.range_eq_toFinset (n : ℕ) : Finset.range n = (List.range n).toFinset :=
  Multiset.toFinset_eq _

/-- The factorial function is primitve recursive. -/
theorem Primrec.factorial : Primrec Nat.factorial := by
  convert list_foldl (σ := ℕ) (h := fun n ⟨p, k⟩ ↦ p * (k + 1)) list_range (const 1) ?_
  · rw [← Finset.prod_range_add_one_eq_factorial, ← List.foldl_map, ← List.prod_eq_foldl]
    rw [← List.prod_toFinset _ List.nodup_range, Finset.range_eq_toFinset]
  · refine comp₂ ?_ .right
    exact nat_mul.comp₂ .left (succ.comp₂ .right)
