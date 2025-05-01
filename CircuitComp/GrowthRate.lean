import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.Partrec

import Mathlib.Tactic.Peel

/-!
# Asymptotic Growth Rates

This file collects about popular "growth rates" that show up in complexity theory. While
`IsBigO` expresses growth rate up to a multiplicative constant, other important classes
include (in rough order of literature frequency):
 * `GrowthRate.poly`: Polynomial growth, typically written $poly(n)$
 * `GrowthRate.polylog`: `(log n)^k`, that is, a polynomial in the logarithm.
 * `GrowthRate.exp`: Exponential growth with any rate, often written $exp(O(n))$
 * `GrowthRate.quasilinear`: Growth as $O(n * (log n)^k)$
 * `GrowthRate.quasipoly`: Growth as $O(2 ^ (log n)^k)$
 * `GrowthRate.computable`: Any computable function. This excludes, for instane, the Busy
    Beaver function.

These are all given as a `Set : ℕ → ℕ`. We have `GrowthRate.bigO` as a thin wrapper
around `Asymptotics.IsBigO`.

We also provide aliases for some of the more common Big-O classes, in order to work
with them more cleanly.
 * `GrowthRate.const`: O(1)
 * `GrowthRate.log`: O(log n)
 * `GrowthRate.sqrt`: O(sqrt n)
 * `GrowthRate.sublinear`: o(n)
 * `GrowthRate.linear`: O(n)
 * `GrowthRate.linearithmic`: O(n * log n)
 * `GrowthRate.two_pow`: O(2 ^ n)
 * `GrowthRate.e_pow`: O(Real.exp n)

Where they involve functions with different definitions on
distinct types (e.g. `Nat.sqrt` vs. `Real.sqrt`, or `(2 : ℕ) ^ ·` vs. `(2 : ℝ) ^ .`), we
want to have both forms.

Since all of these rates are `Set`s, their ordering of "faster growth" is given by the
subset relation `⊆`. That is, where you might want to write `f ≤ g` where `f` and `g`
are growth rates, this is best written as `f ⊆ g`.

-/

abbrev GrowthRate := Set (ℕ → ℕ)

namespace GrowthRate

def bigO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =O[.atTop] (g · : ℕ → ℤ)

section defs
--Defining the rate classes, sorted in order of going faster

abbrev const := bigO 1

abbrev log := bigO Nat.log2

abbrev polylog : Set (ℕ → ℕ) :=
  show GrowthRate from
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(Nat.log2 n ^ C) : ℕ → ℤ)

abbrev sqrt := bigO Nat.sqrt

def sublinear : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =o[.atTop] (· : ℕ → ℤ)

abbrev linear := bigO id

abbrev linarithmic := bigO (fun n ↦ n * Nat.log2 n)

def quasilinear : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n * Nat.log2 n ^ C) : ℕ → ℤ)

def poly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (· ^ C : ℕ → ℤ)

def quasipoly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log2 n ^ C) : ℕ → ℤ)

abbrev two_pow : GrowthRate := bigO (2 ^ ·)

def e_pow : GrowthRate := bigO (⌈Real.exp ·⌉₊)

def exp : GrowthRate :=
  setOf <| fun f ↦ ∃ (C : ℕ),
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ n : ℕ → ℤ)

def computable : GrowthRate :=
  --We can't just define this as `fun f ↦ Nat.Primrec f`, because this would exclude for instance
  --the function `fun n ↦ if HaltingProblem n then 0 else 1`, even though that's O(1). We need to
  --say that this is bigO of some other computable function which gives an upper bound.
  setOf <| fun f ↦ ∃ g,
    Nat.Primrec g ∧ f ∈ bigO g

end defs

section real
--Equivalent versions in terms of BigO real functions

theorem log_iff_rlog {f : ℕ → ℕ} : f ∈ log ↔ (f · : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
  sorry

theorem polylog_iff_rlog {f : ℕ → ℕ} : f ∈ polylog ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ (Real.log n) ^ C : ℕ → ℝ) := by
  sorry

theorem sqrt_iff_rsqrt {f : ℕ → ℕ} : f ∈ sqrt ↔ (f · : ℕ → ℝ) =O[.atTop] (Real.sqrt ·) := by
  sorry

theorem linarithmic_iff_rlog {f : ℕ → ℕ} : f ∈ linarithmic ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ x * Real.log x) := by
  sorry

theorem quasilinear_iff_rlog {f : ℕ → ℕ} : f ∈ quasilinear ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n * (Real.log n) ^ C : ℕ → ℝ) := by
  sorry

theorem poly_iff_rpow {f : ℕ → ℕ} : f ∈ poly ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n ^ C : ℕ → ℝ) := by
  sorry

theorem quasipoly_iff_real_two_pow {f : ℕ → ℕ} : f ∈ quasipoly ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log2 n ^ C) : ℕ → ℝ) := by
  sorry

theorem quasipoly_iff_real_const_pow {f : ℕ → ℕ} : f ∈ quasipoly ↔
    ∃ A C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ A ^ (Nat.log2 n ^ C) : ℕ → ℝ) := by
  sorry

theorem e_pow_iff_rexp {f : ℕ → ℕ} : f ∈ e_pow ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp x) := by
  sorry

theorem exp_iff_rpow {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ C ^ x : ℕ → ℝ) := by
  sorry

theorem exp_iff_rexp_mul {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp (C * x) : ℕ → ℝ) := by
  sorry

end real

section ordering

theorem const_ssubset_log : const ⊂ log := by
  simp only [const, log, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset,
    Pi.one_apply, Nat.cast_one]
  --this seems harder than it "ought" to be.
  constructor
  · intro f hf
    sorry
  · simp only [Asymptotics.isBigO_one_iff, Int.norm_natCast, not_forall, Classical.not_imp]
    use Nat.log2
    constructor
    · simp only [Filter.isBoundedUnder_iff_eventually_bddAbove, Filter.eventually_atTop]
      push_neg
      rintro s ⟨c, hc⟩ a
      use max a (2 ^ ⌈c + 1⌉₊)
      constructor
      · apply Nat.le_max_left
      · suffices ∀ x ∈ s, x < max a (2 ^ ⌈c + 1⌉₊) by
          sorry
        simp [upperBounds] at hc
        peel hc with x hx₁ hx₂
        suffices x < 2 ^ ⌈c + 1⌉₊ by
          exact lt_sup_of_lt_right this
        sorry
    · exact Asymptotics.isBigO_refl (fun x ↦ (Nat.log2 x : ℤ)) Filter.atTop

theorem log_ssubset_polylog : log ⊂ polylog := by
  sorry

theorem polylog_ssubset_sqrt : polylog ⊂ sqrt := by
  sorry

theorem sqrt_ssubset_sublinear : sqrt ⊂ sublinear := by
  sorry

theorem sublinear_ssubset_linear : sublinear ⊂ linear := by
  simp only [sublinear, linear, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset,
    Pi.one_apply, Nat.cast_one]
  constructor
  · intro f hf
    exact hf.isBigO
  · push_neg
    use id
    constructor
    · apply Asymptotics.isBigO_refl
    · apply Asymptotics.isLittleO_irrefl'
      apply Filter.Eventually.frequently
      simp only [id_eq, Int.norm_natCast, ne_eq, Nat.cast_eq_zero, Filter.eventually_atTop]
      use 1
      intro b hb
      exact Nat.ne_zero_of_lt hb

theorem linear_ssubset_linarithmic : linear ⊂ linarithmic := by
  sorry

theorem linarithmic_ssubset_quasilinear : linarithmic ⊂ quasilinear := by
  sorry

theorem quasilinear_ssubset_poly : quasilinear ⊂ poly := by
  sorry

theorem poly_ssubset_quasipoly : poly ⊂ quasipoly := by
  sorry

theorem quasipoly_ssubset_two_pow : quasipoly ⊂ two_pow := by
  sorry

theorem two_pow_ssubset_e_pow : two_pow ⊂ e_pow := by
  sorry

theorem e_pow_ssubset_exp : e_pow ⊂ exp := by
  sorry

theorem exp_ssubset_computable : exp ⊂ computable := by
  sorry

end ordering

end GrowthRate
