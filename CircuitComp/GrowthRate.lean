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

import CircuitComp.ForMathlib

/-!
# Asymptotic Growth Rates

This file collects about common "growth rates" that show up in complexity theory. While
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
--Defining the rate classes, sorted in order of growing more quickly.
--Summary:

/-
const       := bigO 1
log         := bigO (Nat.log 2)
polylog     := setOf ...
sqrt        := bigO Nat.sqrt
sublinear   := setOf ...
linear      := bigO id
linarithmic := bigO (fun n ↦ n * Nat.log 2 n)
quasilinear := setOf ...
poly        := setOf ...
quasipoly   := setOf ...
two_pow     := bigO (2 ^ ·)
e_pow       := bigO (⌈Real.exp ·⌉₊)
exp         := setOf ...
primitiveRecursive := setOf ...
computable := setOf ...
-/

/-- Constant growth rates: `O(1)` -/
abbrev const := bigO 1

/-- Logarithmic growth rates: `O(log n)` -/
abbrev log := bigO (Nat.log 2)

/-- Polylogarithmic growth rates: `(log n) ^ O(1)` -/
abbrev polylog : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Square-root growth rates: `O(√n)` -/
abbrev sqrt := bigO Nat.sqrt

/-- Sublinear growth rates: `o(n)` -/
def sublinear : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =o[.atTop] (· : ℕ → ℤ)

/-- Linear growth rates: `O(n)` -/
abbrev linear := bigO id

/-- Linarithmic growth rates: `O(n * log n)` -/
abbrev linarithmic := bigO (fun n ↦ n * Nat.log 2 n)

/-- Quasilinear growth rates: `n * (log n)^O(1)` -/
def quasilinear : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n * Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Polynomial growth rates: `n ^ O(1)` -/
def poly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (· ^ C : ℕ → ℤ)

/-- Quasipolynomial growth rates: `2 ^ {log(n) ^ O(1)}` -/
def quasipoly : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ)

/-- `O(2 ^ n)` growth rates, not to be confused with `exp` which is `2 ^ O(n)`. -/
abbrev two_pow := bigO (2 ^ ·)

/-- `O(e ^ n)` growth rates, not to be confused with `exp` which is `e ^ O(n)`. -/
abbrev e_pow := bigO (⌈Real.exp ·⌉₊)

/-- Exponential growth rates: `O(1) ^ n`, or equivalently `2 ^ O(n)`. Corresponds to the complexity class `E`. -/
def exp : GrowthRate :=
  setOf <| fun f ↦ ∃ (C : ℕ),
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ n : ℕ → ℤ)

/-- Primitive recursive growth rates.

We can't just define this as the set `fun f ↦ Primrec f`, because this would exclude for
instance the function `fun n ↦ if HaltingProblem n then 0 else 1`, even though that's O(1). We
instead say that this is `bigO` of some other primitive recursive function which gives an upper bound.
-/
def primitiveRecursive : GrowthRate :=
  setOf <| fun f ↦ ∃ g,
    Nat.Primrec g ∧ f ∈ bigO g

/-- Computable growth rates.

We can't just define this as the set `fun f ↦ Computable f`, because this would exclude for
instance the function `fun n ↦ if HaltingProblem n then 0 else 1`, even though that's O(1). We
instead say that this is `bigO` of some other computable function which gives an upper bound.
-/
def computable : GrowthRate :=
  setOf <| fun f ↦ ∃ g,
    Computable g ∧ f ∈ bigO g

end defs

section real
--Equivalent versions in terms of BigO real functions

theorem log_iff_rlog {f : ℕ → ℕ} : f ∈ log ↔ (f · : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
  sorry

theorem polylog_iff_rlog {f : ℕ → ℕ} : f ∈ polylog ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ (Real.log n) ^ C : ℕ → ℝ) := by
  sorry

theorem sqrt_iff_rsqrt {f : ℕ → ℕ} : f ∈ sqrt ↔ (f · : ℕ → ℝ) =O[.atTop] (Real.sqrt ·) := by
  simp [Asymptotics.isBigO_iff', sqrt, abs_of_nonneg, Real.sqrt_nonneg, bigO, Set.mem_setOf_eq]
  constructor <;> rintro ⟨w, hw, k, h⟩
  · refine ⟨w, hw, k, fun n hn ↦ (h n hn).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _) hw.le
  · refine ⟨w * 2, by positivity, k, fun m hm ↦ (h m hm).trans ?_⟩
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    rw [Real.sqrt_le_left (by positivity)]
    norm_cast
    nlinarith only [m.lt_succ_sqrt]

theorem linarithmic_iff_rlog {f : ℕ → ℕ} : f ∈ linarithmic ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ x * Real.log x) := by
  sorry

theorem quasilinear_iff_rlog {f : ℕ → ℕ} : f ∈ quasilinear ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n * (Real.log n) ^ C : ℕ → ℝ) := by
  sorry

theorem poly_iff_rpow {f : ℕ → ℕ} : f ∈ poly ↔
    ∃ (C : ℝ), (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n ^ C : ℕ → ℝ) := by
  simp only [poly, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop,
     Set.mem_setOf_eq, Real.norm_eq_abs, Nat.abs_cast]
  use fun ⟨C, c, a, h⟩ ↦ ⟨C, c, a, fun b hb ↦ by simpa using h b hb⟩
  refine fun ⟨C, c, a, h⟩ ↦ ⟨Nat.ceil C, Max.max c 1, a + 1, fun b hb ↦ (h b (by linarith)).trans ?_⟩
  refine mul_le_mul (le_max_left c 1) ?_ (by positivity) (by positivity)
  rw [abs_of_nonneg (by positivity)]
  exact (Real.rpow_le_rpow_of_exponent_le (mod_cast by linarith) (Nat.le_ceil C)).trans (by norm_num)

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

section closure

variable {f g : ℕ → ℕ}

/-
const       := bigO 1
log         := bigO (Nat.log 2)
polylog     := setOf ...
sqrt        := bigO Nat.sqrt
sublinear   := setOf ...
linear      := bigO id
linarithmic := bigO (fun n ↦ n * Nat.log 2 n)
quasilinear := setOf ...
poly        := setOf ...
quasipoly   := setOf ...
two_pow     := bigO (2 ^ ·)
e_pow       := bigO (⌈Real.exp ·⌉₊)
exp         := setOf ...
primitiveRecursive := setOf ...
computable := setOf ...
-/

section add

theorem const_of_add (hf : f ∈ const) (hg : g ∈ const) : (f + g) ∈ const :=
  hf.add hg

theorem log_of_add (hf : f ∈ log) (hg : g ∈ log) : (f + g) ∈ log :=
  hf.add hg

theorem polylog_of_add (hf : f ∈ polylog) (hg : g ∈ polylog) : (f + g) ∈ polylog := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use Max.max a b
  refine' (ha.trans _ ).add (hb.trans _ )
  all_goals (
    rw [Asymptotics.isBigO_iff]
    use 1
    norm_num
    use 2
    intro _ hn
    exact_mod_cast pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
  )

theorem sqrt_of_add (hf : f ∈ sqrt) (hg : g ∈ sqrt) : (f + g) ∈ sqrt :=
  hf.add hg

theorem sublinear_of_add (hf : f ∈ sublinear) (hg : g ∈ sublinear) : (f + g) ∈ sublinear :=
  hf.add hg

theorem linear_of_add (hf : f ∈ linear) (hg : g ∈ linear) : (f + g) ∈ linear :=
  hf.add hg

theorem linarithmic_of_add (hf : f ∈ linarithmic) (hg : g ∈ linarithmic) : (f + g) ∈ linarithmic :=
  hf.add hg

theorem quasilinear_of_add (hf : f ∈ quasilinear) (hg : g ∈ quasilinear) : (f + g) ∈ quasilinear := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a ⊔ b
  refine' ( Asymptotics.IsBigO.add ( ha.trans ( _ ) ) ( hb.trans ( _ ) ) )
  all_goals ( --TODO: gcongr?
    rw [Asymptotics.isBigO_iff]
    use 1
    norm_num
    use 2
    intro _ hn
    exact_mod_cast Nat.mul_le_mul_left _ <|
      pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
  )

theorem poly_of_add (hf : f ∈ poly) (hg : g ∈ poly) : (f + g) ∈ poly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a ⊔ b
  refine' (ha.trans _ ).add (hb.trans _ )
  all_goals (
    rw [Asymptotics.isBigO_iff]
    use 1
    norm_num
    use 1
    intro _ hn
    exact_mod_cast pow_le_pow_right₀ hn (by bound)
  )

theorem quasipoly_of_add (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : (f + g) ∈ quasipoly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a ⊔ b
  refine' (ha.trans _ ).add (hb.trans _ )
  all_goals (
    rw [Asymptotics.isBigO_iff]
    use 1
    norm_num [Int.norm_eq_abs]
    use 2
    intro _ hn
    exact_mod_cast pow_le_pow_right₀ one_le_two <|
      pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
  )

theorem two_pow_of_add (hf : f ∈ two_pow) (hg : g ∈ two_pow) : (f + g) ∈ two_pow :=
  hf.add hg

theorem e_pow_of_add (hf : f ∈ e_pow) (hg : g ∈ e_pow) : (f + g) ∈ e_pow :=
  hf.add hg

theorem exp_of_add (hf : f ∈ exp) (hg : g ∈ exp) : (f + g) ∈ exp := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a ⊔ b
  refine' (ha.trans _ ).add (hb.trans _ )
  all_goals (
    rw [Asymptotics.isBigO_iff]
    use 1
    norm_num [Int.norm_eq_abs]
    use 2
    intros
    exact pow_le_pow_left₀ (by positivity) (by rw [abs_of_nonneg (by positivity)]; bound) _
  )

theorem primitiveRecursive_of_add (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    (f + g) ∈ primitiveRecursive := by
  obtain ⟨a, ha₁, ha₂⟩ := hf
  obtain ⟨b, hb₁, hb₂⟩ := hg
  use a + b
  rw [← Primrec.nat_iff] at *
  use Primrec.nat_add.comp ha₁ hb₁
  --TODO: Should be its own lemma about bigO on natural functions
  rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff]
  obtain ⟨x, hx₁, hx₂⟩ := ha₂.exists_pos
  obtain ⟨y, hy₁, hy₂⟩ := hb₂.exists_pos
  simp only [Pi.add_apply, Nat.cast_add, Filter.eventually_atTop]
  rw [ Asymptotics.IsBigOWith ] at hx₂ hy₂
  simp_all only [gt_iff_lt, Int.norm_natCast, Filter.eventually_atTop, ge_iff_le]
  obtain ⟨w, h⟩ := hx₂
  obtain ⟨w_1, h_1⟩ := hy₂
  norm_num [ Norm.norm ] at *;
  exact ⟨x ⊔ y, w ⊔ w_1, fun k hk => by
    rw [ abs_of_nonneg ( by positivity : ( f k : ℝ ) + g k ≥ 0 ), abs_of_nonneg ( by positivity : ( a k + b k : ℝ ) ≥ 0 ) ]
    nlinarith [ h k ( le_of_max_le_left hk ), h_1 k ( le_of_max_le_right hk ), le_max_left x y, le_max_right x y ] ⟩

theorem computable_of_add (hf : f ∈ computable) (hg : g ∈ computable) :
    (f + g) ∈ computable := by
  obtain ⟨a, ha₁, ha₂⟩ := hf
  obtain ⟨b, hb₁, hb₂⟩ := hg
  use a + b
  use Primrec.nat_add.to_comp.comp ha₁ hb₁
  --TODO same as above
  sorry

end add
section sub

variable (g)

/--
Proves goals of the form `f - g ∈ S`, where `S` is a `GrowthRate`.
-/
syntax (name := growthRate_sub) "growthRate_sub" : tactic
macro_rules
  | `(tactic| growthRate_sub) => `(tactic| (
    simp only [bigO, exp, polylog, sublinear, quasilinear, poly, quasipoly, primitiveRecursive, computable,
      Asymptotics.isBigO_iff, Asymptotics.isLittleO_iff,
      Int.norm_natCast, Filter.eventually_atTop, Set.mem_setOf_eq] at *
    peel ‹_› with h
    exact (Nat.cast_le.mpr <| Nat.sub_le ..).trans h))

theorem const_of_sub (hf : f ∈ const) : (f - g) ∈ const := by growthRate_sub

theorem log_of_sub (hf : f ∈ log) : (f - g) ∈ log := by growthRate_sub

theorem polylog_of_sub (hf : f ∈ polylog) : (f - g) ∈ polylog := by growthRate_sub

theorem sqrt_of_sub (hf : f ∈ sqrt) : (f - g) ∈ sqrt := by growthRate_sub

theorem sublinear_of_sub (hf : f ∈ sublinear) : (f - g) ∈ sublinear := by growthRate_sub

theorem linear_of_sub (hf : f ∈ linear) : (f - g) ∈ linear := by growthRate_sub

theorem linarithmic_of_sub (hf : f ∈ linarithmic) : (f - g) ∈ linarithmic := by growthRate_sub

theorem quasilinear_of_sub (hf : f ∈ quasilinear) : (f - g) ∈ quasilinear := by growthRate_sub

theorem poly_of_sub (hf : f ∈ poly) : (f - g) ∈ poly := by growthRate_sub

theorem quasipoly_of_sub (hf : f ∈ quasipoly) : (f - g) ∈ quasipoly := by growthRate_sub

theorem two_pow_of_sub (hf : f ∈ two_pow) : (f - g) ∈ two_pow := by growthRate_sub

theorem e_pow_of_sub (hf : f ∈ e_pow) : (f - g) ∈ e_pow := by growthRate_sub

theorem exp_of_sub (hf : f ∈ exp) : (f - g) ∈ exp := by growthRate_sub

theorem primitiveRecursive_of_sub (hf : f ∈ primitiveRecursive) : (f - g) ∈ primitiveRecursive := by growthRate_sub

theorem computable_of_sub (hf : f ∈ computable) : (f - g) ∈ computable := by growthRate_sub

end sub
section mul

theorem const_mul (hf : f ∈ const) (hg : g ∈ const) : (f * g) ∈ const :=
  hf.mul hg

theorem log_mul_const (hf : f ∈ log) (hg : g ∈ const) : (f * g) ∈ log := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem polylog_mul (hf : f ∈ polylog) (hg : g ∈ polylog) : (f * g) ∈ polylog := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem sqrt_mul_const (hf : f ∈ sqrt) (hg : g ∈ const) : (f * g) ∈ sqrt := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem sublinear_mul_const (hf : f ∈ sublinear) (hg : g ∈ const) : (f * g) ∈ sublinear := by
  sorry

theorem linear_mul_const (hf : f ∈ linear) (hg : g ∈ const) : (f * g) ∈ linear := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem linear_of_sqrt_mul_sqrt (hf : f ∈ sqrt) (hg : g ∈ sqrt) : (f * g) ∈ linear := by
  convert hf.mul hg
  sorry

theorem linarithmic_mul_const (hf : f ∈ linarithmic) (hg : g ∈ const) : (f * g) ∈ linarithmic := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem linarithmic_of_linear_mul_log (hf : f ∈ linarithmic) (hg : g ∈ const) : (f * g) ∈ linarithmic := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem quasilinear_mul_polylog (hf : f ∈ quasilinear) (hg : g ∈ polylog) : (f * g) ∈ quasilinear := by
  sorry

theorem poly_mul (hf : f ∈ poly) (hg : g ∈ poly) : (f * g) ∈ poly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem quasipoly_mul (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : (f * g) ∈ quasipoly := by
  sorry

theorem two_pow_mul_const (hf : f ∈ two_pow) (hg : g ∈ const) : (f * g) ∈ two_pow := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem e_pow_mul_const (hf : f ∈ e_pow) (hg : g ∈ const) : (f * g) ∈ e_pow := by
  convert hf.mul hg
  simp only [Pi.one_apply, Nat.cast_one, mul_one]
  rfl

theorem e_pow_of_two_pow_mul_quasipoly (hf : f ∈ two_pow) (hg : g ∈ quasipoly) : (f * g) ∈ e_pow := by
  sorry

theorem exp_mul (hf : f ∈ exp) (hg : g ∈ exp) : (f * g) ∈ exp := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a * b
  convert ha.mul hb
  simp [mul_pow]

theorem primitiveRecursive_mul (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    (f * g) ∈ primitiveRecursive := by
  obtain ⟨a, ha₁, ha₂⟩ := hf
  obtain ⟨b, hb₁, hb₂⟩ := hg
  use a * b
  rw [← Primrec.nat_iff] at *
  use Primrec.nat_mul.comp ha₁ hb₁
  exact ha₂.mul hb₂

theorem computable_mul (hf : f ∈ computable) (hg : g ∈ computable) :
    (f * g) ∈ computable := by
  obtain ⟨a, ha₁, ha₂⟩ := hf
  obtain ⟨b, hb₁, hb₂⟩ := hg
  use a * b
  use Primrec.nat_mul.to_comp.comp ha₁ hb₁
  exact ha₂.mul hb₂

end mul

end closure

section ordering

theorem const_subset_log : const ⊆ log := by
  refine' fun _ h ↦ h.trans _
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun _ hn ↦ ?_⟩
  exact one_le_mul_of_one_le_of_one_le le_rfl (mod_cast Nat.le_log_of_pow_le one_lt_two hn)

theorem const_ssubset_log : const ⊂ log := by
  simp only [const, log, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset,
    Pi.one_apply, Nat.cast_one]
  use const_subset_log
  simp only [Asymptotics.isBigO_one_iff, Int.norm_natCast, not_forall, Classical.not_imp]
  use Nat.log 2
  constructor
  · norm_num [ Filter.IsBoundedUnder, Filter.IsBounded ];
    intro x n;
    cases' exists_nat_gt x with k hk;
    exact ⟨ 2 ^ ( n + k + 1 ), by linarith [ @Nat.lt_two_pow_self ( n + k + 1 ) ], by rw [ Nat.log_pow ( by norm_num ) ] ; simpa using by linarith ⟩
  · apply Asymptotics.isBigO_refl

theorem log_ssubset_polylog : log ⊂ polylog := by
  rw [log, polylog, ssubset_iff_subset_not_subset]
  constructor
  · intro f h
    use 1
    simp_rw [pow_one]
    convert h
  · simp only [bigO, Set.setOf_subset_setOf, forall_exists_index, not_forall,
      Classical.not_imp, exists_and_right]
    use fun n ↦ (Nat.log 2 n) ^ 2, 2, Asymptotics.isBigO_refl ..
    norm_num [Asymptotics.isBigO_iff]
    intro x y
    obtain ⟨n, hn⟩ := exists_nat_gt x
    use 2 ^ (y + n + 1)
    constructor
    · linarith [@Nat.lt_two_pow_self (y + n + 1)]
    · norm_num [Nat.log_pow]
      nlinarith

theorem polylog_subset_sqrt : polylog ⊆ sqrt := by
  intros f hf
  rw [polylog] at hf
  obtain ⟨k, hk⟩ := hf;
  rw [ Asymptotics.isBigO_iff' ] at hk;
  rcases hk with ⟨ c, hc₀, hfc ⟩;
  -- Now consider the inequality $\|f x\| \leq c \| \log^k x \|$ for all sufficiently large $x$.
  have h_bound : ∃ N, ∀ x ≥ N, (f x : ℝ) ≤ c * Real.logb 2 x ^ k := by
    simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
    obtain ⟨w, h⟩ := hfc
    refine ⟨ w + 2, fun x hx ↦ le_trans ( h x <| by linarith ) ?_ ⟩;
    gcongr;
    have : Nat.log 2 x ≤ Real.logb 2 ( x:ℝ ) := by
      rw [ Real.le_logb_iff_rpow_le ( by norm_num ) ( by norm_cast; linarith ) ] ; norm_cast;
      rw [ Nat.pow_le_iff_le_log ] <;> linarith;
    exact this
  obtain ⟨ N, hN ⟩ := h_bound;
  -- Show that $ c * \log^k x \leq \sqrt{x} $ for all sufficiently large $ x $.
  have h_sqrt : ∃ M, ∀ x ≥ M, c * Real.logb 2 x ^ k ≤ Real.sqrt x := by
    -- To prove the bound, we can use the fact that for large enough $x$, $(Real.logb 2 x) ^ k / \sqrt{x}$ tends to $0$.
    have h_limit : Filter.Tendsto (fun x : ℝ => (Real.logb 2 x) ^ k / Real.sqrt x) Filter.atTop (nhds 0) := by
      -- Let `y = log₂ x`, therefore the expression becomes `(y ^ k) / Real.sqrt (2 ^ y)`.
      suffices h_subst : Filter.Tendsto (fun y : ℝ => y ^ k / Real.sqrt (2 ^ y)) Filter.atTop (nhds 0) by
        have := h_subst.comp ( Real.tendsto_logb_atTop ( by norm_num : ( 1 : ℝ ) < 2 ) );
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp ( config := { decide := Bool.true } ) [ Real.sqrt_eq_rpow, Real.rpow_logb, hx ] );
      -- We'll use the exponential property: $\sqrt{2^y} = 2^{y/2}$.
      suffices h_exp : Filter.Tendsto (fun y : ℝ => y ^ k / 2 ^ (y / 2)) Filter.atTop (nhds 0) by
        convert h_exp using 3 ; rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by norm_num ) ] ; ring;
      -- Let `z = y / 2`, therefore the expression becomes `(2z)^k / e^{z * Real.log 2} = 2^k * z^k / e^{z * Real.log 2}`.
      suffices h_z : Filter.Tendsto (fun z : ℝ => (2 ^ k : ℝ) * z ^ k / Real.exp (z * Real.log 2)) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const <| show ( 2 : ℝ ) ⁻¹ > 0 by positivity ) using 2 ; norm_num ; ring;
        simp [ Real.rpow_def_of_pos, mul_assoc, mul_left_comm (Real.log 2) ]
      -- We'll use the fact that $Real.exp (z * Real.log 2)$ grows much faster than $z^k$ for any $k$.
      have h_exp_growth : Filter.Tendsto (fun z : ℝ => z ^ k / Real.exp (z * Real.log 2)) Filter.atTop (nhds 0) := by
        -- Let $y = z \log 2$, therefore the expression becomes $\frac{(y / \log 2)^k}{e^y}$.
        suffices h_subst'' : Filter.Tendsto (fun y : ℝ => (y / Real.log 2) ^ k / Real.exp y) Filter.atTop (nhds 0) by
          convert h_subst''.comp ( Filter.tendsto_id.atTop_mul_const <| Real.log_pos one_lt_two ) using 2 ; norm_num
        -- We'll use the fact that $Real.exp y$ grows much faster than $y^k$.
        have h_exp_y_growth : Filter.Tendsto (fun y : ℝ => y ^ k / Real.exp y) Filter.atTop (nhds 0) := by
          simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
        convert h_exp_y_growth.div_const ( Real.log 2 ^ k ) using 2 <;> ring;
      simpa [ mul_div_assoc ] using h_exp_growth.const_mul _;
    have := h_limit.eventually ( gt_mem_nhds <| show 0 < c⁻¹ from inv_pos.mpr hc₀ );
    simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
    obtain ⟨w, h⟩ := hfc
    obtain ⟨a, h_1⟩ := this
    exact ⟨a ⊔ 2, fun x hx => by
      have := h_1 x ( le_trans ( le_max_left _ _ ) hx ) ;
      have h₂ : 0 < x := by linarith [le_max_left a 2, le_max_right a 2]
      rw [ div_lt_iff₀ (by positivity) ] at this
      nlinarith [ le_max_right a 2, Real.sqrt_nonneg x, inv_mul_cancel₀ <| ne_of_gt hc₀,
        Real.sq_sqrt h₂.le ] ⟩;
  choose M hM using h_sqrt;
  -- Let $x \geq \max(N, M)$.
  have h_final : ∃ K, ∀ x ≥ K, (f x : ℝ) ≤ Real.sqrt x := by
    exact ⟨ ⌈M⌉₊ + N, fun x hx => le_trans ( hN x ( by linarith ) ) ( by simpa using hM x ( le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith ) ) ) ⟩;
  simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
  obtain ⟨w, h⟩ := hfc
  obtain ⟨w_1, h_1⟩ := h_final
  refine' Asymptotics.isBigO_iff.mpr _;
  use 1; norm_num;
  exact ⟨ w_1 + 1, fun b hb => Nat.le_sqrt.mpr <| by have := h_1 b ( le_of_lt hb ) ; rw [ Real.le_sqrt ] at * <;> norm_cast at * <;> linarith ⟩

theorem polylog_ssubset_sqrt : polylog ⊂ sqrt := by
  use polylog_subset_sqrt
  simp only [polylog, sqrt, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset]
  sorry

theorem sqrt_subset_sublinear : sqrt ⊆ sublinear := by
  simp [sqrt, sublinear, bigO]
  intro f hf
  refine hf.trans_isLittleO ?_; clear f hf
  erw [ Asymptotics.isLittleO_iff ];
  intro c a
  simp_all only [Int.norm_natCast, Filter.eventually_atTop, ge_iff_le]
  use Nat.ceil ( ( 1 / c ) ^ 2 );
  intro b hb;
  have : (1 : ℝ) / c ≤ Real.sqrt b := (Real.le_sqrt_of_sq_le <| by simpa using hb );
  rw [ div_le_iff₀ ( by positivity ) ] at this;
  nlinarith [ show ( Nat.sqrt b :ℝ ) ≤ Real.sqrt ↑b by exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' b, Real.sq_sqrt <| Nat.cast_nonneg b ]

theorem sqrt_ssubset_sublinear : sqrt ⊂ sublinear := by
  use sqrt_subset_sublinear
  simp only [sqrt, sublinear, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset]
  sorry

theorem sublinear_ssubset_linear : sublinear ⊂ linear := by
  simp only [sublinear, linear, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset]
  push_neg
  use fun _ ↦ Asymptotics.IsLittleO.isBigO, id, Asymptotics.isBigO_refl ..
  apply Asymptotics.isLittleO_irrefl'
  apply Filter.Eventually.frequently
  rw [Filter.eventually_atTop]
  use 1
  intro b hb
  simp [Nat.ne_zero_of_lt hb]

theorem linear_subset_linarithmic : linear ⊆ linarithmic := by
  refine' fun _ h ↦ h.trans _
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun n hn => ?_⟩
  rw [one_mul]
  exact_mod_cast Nat.le_mul_of_pos_right n (Nat.log_pos one_lt_two hn)

theorem linear_ssubset_linarithmic : linear ⊂ linarithmic := by
  use linear_subset_linarithmic
  simp [linear, linarithmic, bigO]
  use fun n ↦ n * Nat.log 2 n
  use mod_cast Asymptotics.isBigO_refl ..
  norm_num [Asymptotics.isBigO_iff];
  intro x k
  obtain ⟨n, hn⟩ := exists_nat_gt (|x| + 1)
  use 2 ^ (k + n)
  norm_num [Nat.log_pow]
  constructor
  · linarith [@Nat.lt_two_pow_self (k + n)]
  · nlinarith [abs_lt.mp (show |x| < n by linarith), show 0 < (2:ℝ) ^ (k + n) by positivity ]

theorem linarithmic_subset_quasilinear : linarithmic ⊆ quasilinear :=
  fun _ _ ↦ ⟨1, by simpa⟩

theorem linarithmic_ssubset_quasilinear : linarithmic ⊂ quasilinear := by
  use linarithmic_subset_quasilinear
  simp only [quasilinear, bigO, Set.setOf_subset_setOf, not_forall, exists_prop]
  use fun n ↦ n * (Nat.log 2 n) ^ 2
  constructor
  · use 2, mod_cast Asymptotics.isBigO_refl ..
  · norm_num [Asymptotics.isBigO_iff', ← mul_assoc]
    intro x _ y
    obtain ⟨n, _⟩ := exists_nat_gt x
    refine ⟨2 ^ (y + n + 1), le_trans (by linarith) Nat.lt_two_pow_self.le, ?_⟩
    rw [Nat.log_pow Nat.one_lt_ofNat]
    push_cast
    nlinarith [(by positivity : 0 < (2 : ℝ) ^ (y + n + 1) * (y + n + 1))]

theorem quasilinear_subset_poly : quasilinear ⊆ poly := by
  sorry

theorem quasilinear_ssubset_poly : quasilinear ⊂ poly := by
  use quasilinear_subset_poly
  sorry

theorem poly_subset_quasipoly : poly ⊆ quasipoly := by
  refine fun f ⟨c, hf⟩ ↦ ⟨c + 1, hf.trans ?_⟩
  simp only [Asymptotics.isBigO_iff, norm_pow, Int.norm_natCast, Filter.eventually_atTop]
  use 1, 2^(c+1)
  intro b hb
  erw [Real.norm_of_nonneg <| by positivity]
  have h : (b : ℝ) ^ c ≤ (2 : ℝ) ^ ((Nat.log 2 b) * (c + 1)) := by
    have h₁ : b ^ c ≤ 2 ^ ((Nat.log 2 b) * c) * 2 ^ c := by
      rw [pow_mul, ← mul_pow, ← pow_succ]
      exact_mod_cast Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two b).le c;
    norm_cast
    rw [Nat.mul_succ, pow_add]
    refine h₁.trans <| Nat.mul_le_mul_left _ ?_
    refine pow_le_pow_right₀ one_le_two <| Nat.le_log_of_pow_le one_lt_two ?_
    linarith [pow_succ 2 c]
  apply h.trans
  rcases hk : Nat.log 2 b with (_ | k)
  · simp
  rcases c with (_ | c)
  · simp
  rw [one_mul]
  apply pow_le_pow_right₀ one_le_two
  norm_num [Nat.log_eq_iff, Nat.pow_succ, mul_comm (k + 1)] at *
  have h₂ : 1 < k + 1 := Nat.succ_lt_succ <| Nat.pos_of_ne_zero <| by
    rintro rfl
    linarith [c.lt_two_pow_self]
  nlinarith [c.lt_pow_self h₂, (2).lt_pow_self h₂]


theorem poly_ssubset_quasipoly : poly ⊂ quasipoly := by
  use poly_subset_quasipoly
  sorry

theorem quasipoly_ssubset_two_pow : quasipoly ⊂ two_pow := by
  sorry

theorem two_pow_ssubset_e_pow : two_pow ⊂ e_pow := by
  sorry

theorem e_pow_subset_exp : e_pow ⊆ exp := by
  refine' fun f h ↦ ⟨⌈Real.exp 1⌉₊, h.trans (Asymptotics.isBigO_iff.mpr ⟨1, _⟩)⟩
  have h_exp_growth (x : ℕ) : Real.exp x ≤ ⌈Real.exp 1⌉₊ ^ x := by
    simpa using pow_le_pow_left₀ (by positivity) (Nat.le_ceil (Real.exp 1)) x;
  simp only [Int.norm_natCast, Filter.eventually_atTop]
  use 1
  intros
  erw [Real.norm_of_nonneg (by positivity)]
  exact_mod_cast le_trans (Nat.ceil_mono <| h_exp_growth _) (by norm_num)

theorem e_pow_ssubset_exp : e_pow ⊂ exp := by
  use e_pow_subset_exp
  rw [Set.not_subset]
  use (3 ^ ·), ⟨3, by simpa using Asymptotics.isBigO_refl ..⟩
  simp only [e_pow, bigO, Set.mem_setOf_eq, Nat.cast_pow, Nat.cast_ofNat]
  intro h
  rw [Asymptotics.isBigO_iff'] at h
  contrapose! h;
  intro c _
  have h_exp : Filter.Tendsto (fun x : ℕ => (3 ^ x : ℝ) / ⌈(Real.exp x)⌉₊) Filter.atTop Filter.atTop := by
    have h_exp_approx : ∀ n : ℕ, (3 ^ n : ℝ) / ⌈(Real.exp n)⌉₊ ≥ (3 / Real.exp 1) ^ n / 2 := by
      intro n
      rw [div_pow, Real.exp_one_pow, div_div, ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left ((Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith [Real.add_one_le_exp n])) (by positivity)
    refine Filter.tendsto_atTop_mono h_exp_approx ?_
    refine Filter.Tendsto.atTop_div_const (by positivity) (tendsto_pow_atTop_atTop_of_one_lt ?_)
    rw [one_lt_div (by positivity)]
    exact Real.exp_one_lt_d9.trans_le <| by norm_num
  replace h_exp := h_exp.eventually_gt_atTop c
  simp only [Filter.eventually_atTop, ge_iff_le, Int.norm_natCast, not_exists, not_forall, not_le, exists_prop] at h_exp ⊢
  intro x
  rcases h_exp with ⟨w, h⟩
  refine ⟨_, Nat.le_add_left x w, ?_⟩
  erw [Real.norm_of_nonneg (by positivity)]
  specialize h (w + x) (by linarith)
  rw [lt_div_iff₀ (by positivity)] at h
  exact_mod_cast h

theorem exp_subset_primitiveRecursive : exp ⊆ primitiveRecursive := by
  rintro f ⟨k, hk⟩
  constructor
  constructor
  swap
  norm_cast at hk
  simpa using Nat.Primrec.pow.comp (.pair (.const k) .id)

/-- The factorial function is not in `exp`. -/
theorem factorial_not_mem_exp : Nat.factorial ∉ exp := by
  rintro ⟨c, hc⟩
  rw [Asymptotics.isBigO_iff] at hc
  contrapose! hc
  simp only [Filter.eventually_atTop, not_exists, not_forall]
  intro y z
  -- We'll use the exponential property: the factorial grows faster than any exponential function.
  have hf_growth : Filter.Tendsto (fun n => (y * (c ^ n) : ℝ) / n.factorial) Filter.atTop (nhds 0) := by
    have h := FloorSemiring.tendsto_pow_div_factorial_atTop (c : ℝ)
    simpa [ mul_div_assoc ] using h.const_mul y
  obtain ⟨w, h⟩ := Filter.eventually_atTop.mp <| hf_growth.eventually (gt_mem_nhds zero_lt_one)
  refine ⟨_, le_max_left z w, ?_⟩
  specialize h _ (le_max_right z w)
  rw [div_lt_one (by positivity)] at h
  simpa using h

theorem exp_ssubset_primitiveRecursive : exp ⊂ primitiveRecursive := by
  use exp_subset_primitiveRecursive
  rw [Set.not_subset]
  use Nat.factorial
  constructor
  · use Nat.factorial
    rw [← Primrec.nat_iff]
    exact ⟨Primrec.factorial, Asymptotics.isBigO_refl ..⟩
  · exact factorial_not_mem_exp

theorem primitiveRecursive_subset_computable : primitiveRecursive ⊆ computable := by
  rintro f ⟨g, hg⟩
  rw [← Primrec.nat_iff] at hg
  exact ⟨g, hg.left.to_comp, hg.right⟩

theorem primitiveRecursive_ssubset_computable : primitiveRecursive ⊂ computable := by
  use primitiveRecursive_subset_computable
  rw [Set.not_subset]
  use (fun x ↦ ack x x)
  simp [primitiveRecursive, exp, bigO]
  constructor
  · --have := computable₂_ack --BUMP mathlib
    sorry
  · sorry

end ordering

end GrowthRate
