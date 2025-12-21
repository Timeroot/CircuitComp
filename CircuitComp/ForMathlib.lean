import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.Partrec
import Mathlib.Computability.Ackermann
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Floor

import Mathlib.Tactic.Peel
import Mathlib.Tactic.Bound

/-- The factorial function is primitve recursive. -/
theorem Primrec.factorial : Primrec Nat.factorial := by
  convert list_foldl (σ := ℕ) (h := fun n ⟨p, k⟩ ↦ p * (k + 1)) list_range (const 1) ?_
  · rw [← Finset.prod_range_add_one_eq_factorial, ← List.foldl_map, ← List.prod_eq_foldl]
    rw [← List.prod_toFinset _ List.nodup_range, ← List.toFinset_range]
  · refine comp₂ ?_ .right
    exact nat_mul.comp₂ .left (succ.comp₂ .right)

/- Snippet that forces Aesop to be terminal-only.-/
namespace TerminalAesop

syntax (name := terminalAesop) "aesop" : tactic

macro_rules (kind := terminalAesop)
  | `(tactic| aesop) =>
    `(tactic| aesop (config := {terminal := true}))

syntax (name := terminalBound) "bound" : tactic

open Mathlib.Tactic in
macro_rules (kind := terminalBound)
  | `(tactic| bound) =>
    `(tactic| aesop (rule_sets := [Bound, -default]) (config := Bound.boundConfig) (config := {terminal := true}))

end TerminalAesop
