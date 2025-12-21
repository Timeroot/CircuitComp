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

/-- A **Growth rate** is just any collection of Nat functions, but as a type alias intended for
discussing how quickly certain classes functions grow, as is often needed in asymptotic runtime
or memory analysis in computational complexity theory.
-/
abbrev GrowthRate := Set (ℕ → ℕ)

namespace GrowthRate

def bigO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =O[.atTop] (g · : ℕ → ℤ)

def littleO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =o[.atTop] (g · : ℕ → ℤ)

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
def polylog : GrowthRate :=
  setOf <| fun f ↦ ∃ C,
    (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(Nat.log 2 n ^ C) : ℕ → ℤ)

/-- Square-root growth rates: `O(√n)` -/
abbrev sqrt := bigO Nat.sqrt

/-- Sublinear growth rates: `o(n)` -/
abbrev sublinear := littleO id

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

section basic

/-
If a function `f : ℕ → ℕ` has constant growth rate (i.e., is O(1)), then it is bounded by some constant `C`.
-/
lemma bounded_of_const {f : ℕ → ℕ} (h : f ∈ GrowthRate.const) : ∃ C, ∀ n, f n ≤ C := by
  have := Asymptotics.isBigO_iff.mp h;
  simp_all only [norm_natCast, Pi.one_apply, Nat.cast_one, norm_one, mul_one, Filter.eventually_atTop, ge_iff_le]
  obtain ⟨w, h_1⟩ := this
  obtain ⟨w_1, h_1⟩ := h_1
  -- Consider the maximum value that f can take on for inputs less than w_1. Since there are only finitely many such inputs (from 0 to w_1-1), there must be a maximum value among them. Let's call this maximum value M.
  obtain ⟨M, hM⟩ : ∃ M, ∀ n < w_1, f n ≤ M := by
    exact ⟨ Finset.sup ( Finset.range w_1 ) f, fun n hn => Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
  exact ⟨ ⌈w⌉₊ + M, fun n => if hn : n < w_1 then le_trans ( hM n hn ) ( Nat.le_add_left _ _ ) else le_trans ( Nat.cast_le.mp ( le_trans ( h_1 n ( le_of_not_gt hn ) ) ( Nat.le_ceil _ ) ) ) ( Nat.le_add_right _ _ ) ⟩

theorem bigO_add {f g a b: ℕ → ℕ} (hf : f ∈ bigO a) (hg : g ∈ bigO b) : f + g ∈ bigO (a + b) := by
  rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff]
  obtain ⟨x, hx₁, hx₂⟩ := hf.exists_pos
  obtain ⟨y, hy₁, hy₂⟩ := hg.exists_pos
  simp only [Pi.add_apply, Nat.cast_add, Filter.eventually_atTop]
  rw [ Asymptotics.IsBigOWith ] at hx₂ hy₂
  simp_all only [gt_iff_lt, Int.norm_natCast, Filter.eventually_atTop, ge_iff_le]
  obtain ⟨w, h⟩ := hx₂
  obtain ⟨w_1, h_1⟩ := hy₂
  norm_num [Norm.norm]
  exact ⟨x ⊔ y, w ⊔ w_1, fun k hk => by
    rw [ abs_of_nonneg ( by positivity : ( f k : ℝ ) + g k ≥ 0 ), abs_of_nonneg ( by positivity : ( a k + b k : ℝ ) ≥ 0 ) ]
    nlinarith [ h k ( le_of_max_le_left hk ), h_1 k ( le_of_max_le_right hk ), le_max_left x y, le_max_right x y ] ⟩

end basic

section lawful

/-- We call a `GrowthRate` *lawful* if it is closed under dominating sequences
and addition. This is enough to get most desirable properties. For instance,
all big-O and little-O rates are lawful, as is `poly`. -/
class LawfulGrowthRate (S : GrowthRate) : Prop where
  /-- If a function `f` is in S and it dominates `g` (is eventually greater than g), then `g ∈ S`. -/
  mem_dominating {f g : ℕ → ℕ} : (∀ᶠ x in .atTop, g x ≤ f x) → (f ∈ S) → g ∈ S
  /-- S is closed under addition. -/
  mem_add {f g : ℕ → ℕ} : (f ∈ S) → (g ∈ S) → (f + g ∈ S)

instance instLawfulBigO (f : ℕ → ℕ) : LawfulGrowthRate (bigO f) where
  mem_dominating h hf := by
    simp only [bigO, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop] at h hf ⊢
    obtain ⟨a₁, hf₁⟩ := h
    obtain ⟨c, a₂, hg⟩ := hf
    refine ⟨c, max a₁ a₂, fun b hb ↦ ?_⟩
    exact le_trans (mod_cast hf₁ b (le_of_max_le_left hb)) (hg b (le_of_max_le_right hb))
  mem_add hf hg := hf.add hg

instance instLawfulLittleO (f : ℕ → ℕ) : LawfulGrowthRate (littleO f) where
  mem_dominating h hf := by
    simp only [Filter.eventually_atTop, littleO, Asymptotics.isLittleO_iff, Int.norm_natCast] at h hf ⊢
    intro c₀ hc₀
    obtain ⟨a₁, hf₁⟩ := h
    obtain ⟨a₂, hg⟩ := hf hc₀
    refine ⟨max a₁ a₂, fun b hb ↦ ?_⟩
    exact le_trans (mod_cast hf₁ b (le_of_max_le_left hb)) (hg b (le_of_max_le_right hb))
  mem_add hf hg := hf.add hg

instance : LawfulGrowthRate const := instLawfulBigO _

instance : LawfulGrowthRate log := instLawfulBigO _

instance : LawfulGrowthRate polylog where
  mem_dominating h hf := by
    simp only [polylog, Filter.eventually_atTop, Asymptotics.isBigO_iff, norm_natCast,
      Nat.cast_pow, Set.mem_setOf] at h hf ⊢
    choose C c a hC using hf
    choose a₂ h using h
    use C, c, a₂ + a
    intro n hn
    grw [h n (by omega), hC n (by omega)]
  mem_add hf hg := by
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num
      use 2
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
    )

instance : LawfulGrowthRate sqrt := instLawfulBigO _

instance : LawfulGrowthRate sublinear := instLawfulLittleO _

instance : LawfulGrowthRate linear := instLawfulBigO _

instance : LawfulGrowthRate linarithmic := instLawfulBigO _

instance : LawfulGrowthRate quasilinear where
  mem_dominating h hf := by
    rcases hf with ⟨C, hC⟩
    refine ⟨C, Asymptotics.IsBigO.trans ?_ hC⟩
    rw [Asymptotics.isBigO_iff]
    use 1
    aesop
  mem_add hf hg := by
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num
      use 2
      intro _ hn
      exact_mod_cast Nat.mul_le_mul_left _ <|
        pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
    )

instance : LawfulGrowthRate poly where
  mem_dominating h hf := by
    simp_rw [poly, Set.mem_setOf, Asymptotics.isBigO_iff] at hf ⊢
    obtain ⟨p, c, hf⟩ := hf
    use p, c
    filter_upwards [h, hf] with a h ha
    simp at ha ⊢
    exact le_trans (mod_cast h) ha
  mem_add hf hg := by
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num
      use 1
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ hn (by bound)
    )

instance : LawfulGrowthRate quasipoly where
  mem_dominating h hf := by
    simp only [quasipoly, Filter.eventually_atTop, Asymptotics.isBigO_iff, norm_natCast,
      Set.mem_setOf] at h hf ⊢
    choose C c a hC using hf
    choose a₂ h using h
    use C, c, a₂ + a
    intro n hn
    grw [h n (by omega), hC n (by omega)]
  mem_add hf hg := by
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num [Int.norm_eq_abs]
      use 2
      intro _ hn
      exact_mod_cast pow_le_pow_right₀ one_le_two <|
        pow_le_pow_right₀ (Nat.le_log_of_pow_le one_lt_two hn) (by bound)
    )

instance : LawfulGrowthRate two_pow := instLawfulBigO _

instance : LawfulGrowthRate e_pow := instLawfulBigO _

instance : LawfulGrowthRate exp where
  mem_dominating h hf := by
    simp only [exp, Filter.eventually_atTop, Asymptotics.isBigO_iff, norm_natCast,
      Set.mem_setOf] at h hf ⊢
    choose C c a hC using hf
    choose a₂ h using h
    use C, c, a₂ + a
    intro n hn
    grw [h n (by omega), hC n (by omega)]
  mem_add hf hg := by
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    use a + b
    refine Asymptotics.IsBigO.add (ha.trans ?_) (hb.trans ?_)
    all_goals (
      rw [Asymptotics.isBigO_iff]
      use 1
      norm_num [Int.norm_eq_abs]
      use 2
      intros
      exact pow_le_pow_left₀ (by positivity) (by rw [abs_of_nonneg (by positivity)]; bound) _
    )

instance : LawfulGrowthRate primitiveRecursive where
  mem_dominating h hf := by
    rw [primitiveRecursive, Set.mem_setOf] at hf ⊢
    peel hf with g hg hf
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    refine Asymptotics.IsBigO.trans ?_ hf;
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Filter.eventually_atTop.mpr ⟨N, fun n hn => by simpa using mod_cast hN n hn⟩⟩
  mem_add hf hg := by
    obtain ⟨a, ha₁, ha₂⟩ := hf
    obtain ⟨b, hb₁, hb₂⟩ := hg
    simp_rw [primitiveRecursive, ← Primrec.nat_iff] at *
    exact ⟨_, Primrec.nat_add.comp ha₁ hb₁, bigO_add ha₂ hb₂⟩

instance : LawfulGrowthRate computable where
  mem_dominating h hf := by
    rw [computable, Set.mem_setOf] at hf ⊢
    peel hf with g hg hf
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    refine Asymptotics.IsBigO.trans ?_ hf;
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Filter.eventually_atTop.mpr ⟨N, fun n hn => by simpa using mod_cast hN n hn⟩⟩
  mem_add hf hg := by
    obtain ⟨a, ha₁, ha₂⟩ := hf
    obtain ⟨b, hb₁, hb₂⟩ := hg
    exact ⟨_, Primrec.nat_add.to_comp.comp ha₁ hb₁, bigO_add ha₂ hb₂⟩

variable {f g : ℕ → ℕ} {S : GrowthRate} [LawfulGrowthRate S]

--TODO: Add some kind of Inhabited property to LawfulGrowthRate so that we don't need hf here
theorem zero_mem (hf : f ∈ S) : 0 ∈ S := by
  convert LawfulGrowthRate.mem_dominating _ hf;
  exact Filter.Eventually.of_forall fun _ => Nat.zero_le _;

theorem add (hf : f ∈ S) (hg : g ∈ S) : (f + g) ∈ S := by
  apply LawfulGrowthRate.mem_add hf hg

theorem sub (hf : f ∈ S) (g) : (f - g) ∈ S := by
  apply LawfulGrowthRate.mem_dominating _ hf
  rw [Filter.eventually_atTop]
  exact ⟨0, fun _ _ ↦ (Nat.cast_le.mpr <| Nat.sub_le ..)⟩

theorem mul_const (hf : f ∈ S) (hg : g ∈ const) : (f * g) ∈ S := by
  have h_add {f₁ f₂} : _ := @GrowthRate.add f₁ f₂ (S := S) _
  have ⟨ C, hC ⟩ := bounded_of_const hg
  -- Since $S$ is closed under addition, we can add $f * g$ to itself $C$ times to get $C * (f * g)$, which is in $S$.
  have h_add_const : ∀ {f : ℕ → ℕ} (C : ℕ), f ∈ S → C * f ∈ S := by
    intro f C hf
    induction C <;> simp_all +decide [ add_mul, zero_mem hf ]
  specialize h_add_const C hf
  exact LawfulGrowthRate.mem_dominating ( Filter.eventually_atTop.mpr ⟨ 0, fun n hn => by simpa [ mul_comm ] using Nat.mul_le_mul_right ( f n ) ( hC n ) ⟩ ) h_add_const

end lawful

section equivalent_defs
--Equivalent versions in terms of other functions or big-O-style descriptions

theorem bigO_log2_eq_log : bigO Nat.log2 = log := by
  rw [funext @Nat.log2_eq_log_two]

theorem clog_mem_log2 : Nat.clog 2 ∈ log := by
  rw [← bigO_log2_eq_log]
  -- Since Nat.clog 2 n is either 0 or Nat.log 2 n + 1, we can choose C = 2.
  have h_bound : ∀ n, Nat.clog 2 n ≤ 2 * Nat.log 2 n + 2 := by
    -- By definition of Nat.clog, we have that if Nat.clog 2 n ≤ k, then 2^k ≥ n.
    intro n
    by_cases hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3;
    · rcases hn with ( rfl | rfl | rfl | rfl ) <;> native_decide
    · have h_bound : 2^(2 * Nat.log 2 n + 2) ≥ n := by
        exact le_trans ( Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) )
          ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) );
      exact Nat.le_trans ( Nat.clog_mono_right _ h_bound ) ( by norm_num );
  have h_bigO : ∃ C N, ∀ n ≥ N, Nat.clog 2 n ≤ C * Nat.log2 n := by
    -- C = 4 and N = 2 suffices for the bigO.
    use 4, 2;
    intro n hn;
    rw [ Nat.log2_eq_log_two ];
    linarith [ h_bound n, show Nat.log 2 n ≥ 1 from Nat.le_log_of_pow_le one_lt_two hn ]
  obtain ⟨ C, N, hC ⟩ := h_bigO;
  apply Asymptotics.IsBigO.of_bound C _
  filter_upwards [ Filter.eventually_ge_atTop N ] with n hn
  simpa using mod_cast hC n hn


theorem log_iff_rlog {f : ℕ → ℕ} : f ∈ log ↔ (f · : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
  -- The definition of `GrowthRate.log` is that `f` is `O(log n)`, which is exactly what the `IsBigO` statement is saying.
  simp only [log]
  constructor <;> intro H;
  · rw [ Asymptotics.isBigO_iff ] at *;
    -- Since $Nat.log 2 x \leq Real.log x$ for all $x \geq 2$, we can find a constant $c'$ such that $c * Nat.log 2 x \leq c' * Real.log x$.
    obtain ⟨c, hc⟩ : ∃ c, ∀ᶠ x in Filter.atTop, f x ≤ c * Nat.log 2 x := by
      rw [ GrowthRate.bigO ] at H;
      simp +zetaDelta at *;
      rw [ Asymptotics.isBigO_iff' ] at H;
      norm_num [ Norm.norm ] at H;
      obtain ⟨ c, hc, a, ha⟩ := H
      exact ⟨ ⌈c⌉₊, a, fun n hn => by exact_mod_cast ( by nlinarith [ Nat.le_ceil c, ha n hn ] : ( f n : ℝ ) ≤ ⌈c⌉₊ * Nat.log 2 n ) ⟩ ;
    -- Since $Nat.log 2 x \leq Real.log x$ for all $x \geq 2$, we can find a constant $c'$ such that $c * Nat.log 2 x \leq c' * Real.log x$ for all $x \geq 2$.
    obtain ⟨c', hc'⟩ : ∃ c' : ℝ, ∀ x ≥ 2, Nat.log 2 x ≤ c' * Real.log x := by
      use 1 / Real.log 2;
      intro x hx; rw [ div_mul_eq_mul_div, le_div_iff₀ ( Real.log_pos one_lt_two ) ] ; norm_cast;
      rw [ one_mul, ← Real.log_rpow zero_lt_two ] ; gcongr ; norm_cast ; exact Nat.pow_log_le_self 2 <| by linarith;
    use c * c';
    filter_upwards [hc, Filter.eventually_ge_atTop 2 ] with x hx₁ hx₂
    norm_num [mul_assoc]
    rw [abs_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ]
    exact le_trans ( Nat.cast_le.mpr hx₁ ) ( by simpa using mul_le_mul_of_nonneg_left ( hc' x ( mod_cast hx₂ ) ) ( Nat.cast_nonneg c ) )
  · -- Since $\log_2(x) = \frac{\log(x)}{\log(2)}$, we can use the fact that $f = O(\log(x))$ implies $f = O(\log_2(x))$.
    have h_log2 : (fun x => (f x : ℝ)) =O[Filter.atTop] (fun x => Real.log x / Real.log 2) := by
      rw [ Asymptotics.isBigO_iff' ] at *;
      simp_all [mul_div]
      exact ⟨ H.choose * |Real.log 2|, mul_pos H.choose_spec.1 ( abs_pos.mpr ( ne_of_gt ( Real.log_pos one_lt_two ) ) ), H.choose_spec.2.choose, fun n hn => by rw [ le_div_iff₀ ( abs_pos.mpr ( ne_of_gt ( Real.log_pos one_lt_two ) ) ) ] ; nlinarith [ H.choose_spec.2.choose_spec n hn, abs_pos.mpr ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] ⟩;
    -- Since $\log_2(x) = \frac{\log(x)}{\log(2)}$, we can use the fact that $f = O(\log(x))$ implies $f = O(\log_2(x))$ by the properties of logarithms.
    have h_log2_nat : (fun x => (f x : ℝ)) =O[Filter.atTop] (fun x => (Nat.log 2 x : ℝ)) := by
      refine' h_log2.trans _;
      -- Since $\log_2(x) \geq \frac{\log(x)}{\log(2)} - 1$, we can use the fact that $f = O(\log(x))$ implies $f = O(\log_2(x))$ by the properties of logarithms.
      have h_log2_ge : ∀ x : ℕ, x ≥ 2 → Real.log x / Real.log 2 ≤ Nat.log 2 x + 1 := by
        intro x hx; rw [ div_le_iff₀ ( Real.log_pos one_lt_two ) ] ; norm_cast;
        rw [ ← Real.log_rpow zero_lt_two ] ; gcongr ; norm_cast ; exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by norm_num ) _ );
      refine' Asymptotics.IsBigO.of_bound 2 _;
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; linarith [ h_log2_ge x hx, show ( Nat.log 2 x : ℝ ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le ( by norm_num ) hx ] ;
    convert h_log2_nat using 1;
    simp [GrowthRate.bigO];
    norm_num [ Asymptotics.isBigO_iff ]

theorem polylog_iff_rlog {f : ℕ → ℕ} : f ∈ polylog ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ (Real.log n) ^ C : ℕ → ℝ) := by
  -- To prove the equivalence, we can use the fact that ℤ and ℝ are isomorphic in this context.
  have h_iso : ∀ f g : ℕ → ℤ, (f · : ℕ → ℤ) =O[Filter.atTop] (g · : ℕ → ℤ) ↔ (fun x => f x : ℕ → ℝ) =O[Filter.atTop] (fun n => g n : ℕ → ℝ) := by
    norm_num [ Asymptotics.isBigO_iff ];
    norm_num [ Norm.norm ];
  simp [GrowthRate.polylog, h_iso];
  constructor <;> rintro ⟨ C, hC ⟩ <;> use C <;> refine' hC.trans _;
  · -- We can use the fact that $Real.log (x : ℝ) ≥ Real.log 2 * Nat.log 2 x$ for all $x ≥ 1$.
    have h_log_ge : ∀ x : ℕ, 1 ≤ x → Real.log (x : ℝ) ≥ Real.log 2 * Nat.log 2 x := by
      intro x hx; rw [ mul_comm ] ; rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast; exact Nat.pow_log_le_self 2 ( by positivity ) ) ;
    refine' Asymptotics.IsBigO.of_bound ( ( Real.log 2 ) ⁻¹ ^ C ) _;
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; rw [ inv_pow ] ; exact le_trans ( by ring_nf; norm_num ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( h_log_ge x hx ) _ ) ( by positivity ) ) ;
  · -- Since $\log_2 n \leq \log n / \log 2$, we have $(\log_2 n)^C \leq (\log n / \log 2)^C$.
    have h_log_bound : ∀ n : ℕ, n ≥ 2 → (Real.log n) ^ C ≤ (Nat.log 2 n + 1) ^ C * (Real.log 2) ^ C := by
      intro n hn
      have h_log_bound : Real.log n ≤ (Nat.log 2 n + 1) * Real.log 2 := by
        rw [ ← Real.log_rpow zero_lt_two ] ; gcongr ; norm_cast ; exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by norm_num ) _ );
      simpa only [ mul_pow ] using pow_le_pow_left₀ ( Real.log_nonneg ( by norm_cast; linarith ) ) h_log_bound C;
    -- Since $(Nat.log 2 n + 1)^C \leq 2^C * (Nat.log 2 n)^C$ for $n \geq 2$, we can bound the expression further.
    have h_log_bound_further : ∀ n : ℕ, n ≥ 2 → (Real.log n) ^ C ≤ 2 ^ C * (Nat.log 2 n) ^ C * (Real.log 2) ^ C := by
      intros n hn
      have h_log_bound_further : (Nat.log 2 n + 1) ^ C ≤ 2 ^ C * (Nat.log 2 n) ^ C := by
        rw [ ← mul_pow ] ; gcongr ; linarith [ Nat.log_pos one_lt_two hn ];
      exact le_trans ( h_log_bound n hn ) ( mul_le_mul_of_nonneg_right ( mod_cast h_log_bound_further ) ( by positivity ) );
    refine' Asymptotics.IsBigO.of_bound ( 2 ^ C * Real.log 2 ^ C ) _;
    filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; linarith [ h_log_bound_further n hn ] ;

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
  -- To prove the equivalence, we can use the fact that Nat.log 2 x is asymptotically the same as log x.
  have h_log_equiv : Asymptotics.IsBigO Filter.atTop (fun x : ℕ => (Nat.log 2 x : ℝ)) (fun x : ℕ => Real.log x) ∧ Asymptotics.IsBigO Filter.atTop (fun x : ℕ => Real.log x) (fun x : ℕ => (Nat.log 2 x : ℝ)) := by
    constructor <;> rw [ Asymptotics.isBigO_iff ];
    · use 1 / Real.log 2;
      field_simp;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self 2 <| by linarith ) ;
    · -- We can use the fact that $x < 2^{Nat.log 2 x + 1}$ to show that $Real.log x < (Nat.log 2 x + 1) * Real.log 2$.
      have h_log_bound : ∀ x : ℕ, x ≥ 2 → Real.log x < (Nat.log 2 x + 1) * Real.log 2 := by
        intro x hx; rw [ ← Real.log_rpow zero_lt_two ] ; gcongr ; norm_cast ; exact Nat.lt_pow_succ_log_self ( by decide ) _;
      use 2 * Real.log 2;
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ), Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; nlinarith [ h_log_bound x hx, Real.log_pos one_lt_two, show ( Nat.log 2 x : ℝ ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ] ;
  constructor <;> intro h;
  · -- By combining the results from h and h_log_equiv, we can conclude that f is O(x * Real.log x).
    have h_combined : (fun x : ℕ => (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ => (x * Nat.log 2 x : ℝ)) := by
      -- By definition of GrowthRate.linarithmic, if f is in linarithmic, then f is O(x * Nat.log 2 x).
      have h_def : (fun x : ℕ => (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ => (x * Nat.log 2 x : ℝ)) := by
        convert h using 1;
        -- By definition of GrowthRate.linarithmic, we have that f is in the big-O of x * Nat.log 2 x. Therefore, the equivalence holds.
        simp [GrowthRate.linarithmic, GrowthRate.bigO];
        norm_num [ Asymptotics.isBigO_iff ];
      exact h_def
    apply h_combined.trans
    exact Asymptotics.IsBigO.mul ( Asymptotics.isBigO_refl _ _ ) h_log_equiv.1;
  · -- Since $x \log x$ is equivalent to $x \cdot \text{Nat.log } 2 x$ in terms of growth rate, we can use the fact that $h$ implies $f$ is $O(x \cdot \text{Nat.log } 2 x)$.
    have h_equiv : (fun x : ℕ => (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ => (x : ℝ) * (Nat.log 2 x : ℝ)) := by
      have h_equiv : (fun x : ℕ => (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ => (x : ℝ) * Real.log x) := by
        exact h;
      exact h_equiv.trans ( by simpa using Asymptotics.IsBigO.mul ( Asymptotics.isBigO_refl _ _ ) h_log_equiv.2 );
    convert h_equiv using 1;
    simp [GrowthRate.bigO];
    norm_num [ Asymptotics.isBigO_iff ]

theorem quasilinear_iff_rlog {f : ℕ → ℕ} : f ∈ quasilinear ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n * (Real.log n) ^ C : ℕ → ℝ) := by
  constructor;
  · rintro ⟨ C, hC ⟩;
    -- Since $Nat.log 2 n$ is $O(log n)$, we can replace $Nat.log 2 n$ with $Real.log n$ in the bound.
    have h_log : (fun n => (Nat.log 2 n : ℝ)) =O[Filter.atTop] (fun n => Real.log n) := by
      rw [ Asymptotics.isBigO_iff ];
      -- We can choose $c = \frac{1}{\log 2}$.
      use 1 / Real.log 2;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ] ; simpa using Real.log_le_log ( by positivity ) ( show ( x : ℝ ) ≥ 2 ^ Nat.log 2 x by exact_mod_cast Nat.pow_log_le_self 2 ( by linarith ) ) ;
    have h_replace : (fun n => (n * Nat.log 2 n ^ C : ℝ)) =O[Filter.atTop] (fun n => (n * Real.log n ^ C : ℝ)) := by
      exact Asymptotics.IsBigO.mul ( Asymptotics.isBigO_refl _ _ ) ( h_log.pow _ );
    -- By transitivity of big O notation, we can combine the two results.
    have h_trans : (fun n => (f n : ℝ)) =O[Filter.atTop] (fun n => (n * Nat.log 2 n ^ C : ℝ)) := by
      rw [ Asymptotics.isBigO_iff ] at * ; aesop;
    exact ⟨ C, h_trans.trans h_replace ⟩;
  · simp +zetaDelta at *;
    -- Since the real logarithm and the natural logarithm are related by a constant factor, the equivalence holds.
    intros C hC
    have h_nat_log : ∃ C' : ℕ, (fun x => (f x : ℝ)) =O[Filter.atTop] (fun n => (n : ℝ) * (Nat.log 2 n) ^ C') := by
      refine ⟨C, hC.trans ?_⟩
      have h_log : (fun n : ℕ => Real.log n) =O[Filter.atTop] (fun n : ℕ => (Nat.log 2 n : ℝ)) := by
        have h_log_eq : ∀ n : ℕ, n ≥ 2 → Real.log n ≤ Real.log 2 * Nat.log 2 n + Real.log 2 := by
          intro n hn
          have h_log_bound : n ≤ 2 ^ (Nat.log 2 n + 1) := by
            exact le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ );
          have := Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≤ 2 ^ ( Nat.log 2 n + 1 ) by exact_mod_cast h_log_bound ) ; norm_num [ Real.log_pow ] at * ; linarith;
        rw [ Asymptotics.isBigO_iff ];
        refine' ⟨ Real.log 2 + Real.log 2, Filter.eventually_atTop.mpr ⟨ 2, fun n hn => _ ⟩ ⟩ ; rw [ Real.norm_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ), Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; nlinarith [ h_log_eq n hn, Real.log_pos one_lt_two, show ( Nat.log 2 n : ℝ ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ];
      exact Asymptotics.IsBigO.mul ( Asymptotics.isBigO_refl _ _ ) ( h_log.pow _ );
    -- Since the real logarithm and the natural logarithm are related by a constant factor, the equivalence holds. Therefore, we can conclude that f is in quasilinear.
    simpa [quasilinear, Asymptotics.isBigO_iff] using h_nat_log

theorem poly_iff_rpow {f : ℕ → ℕ} : f ∈ poly ↔
    ∃ (C : ℝ), (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ n ^ C : ℕ → ℝ) := by
  simp only [poly, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop,
     Set.mem_setOf_eq, Real.norm_eq_abs, Nat.abs_cast]
  use fun ⟨C, c, a, h⟩ ↦ ⟨C, c, a, fun b hb ↦ by simpa using h b hb⟩
  refine fun ⟨C, c, a, h⟩ ↦ ⟨Nat.ceil C, Max.max c 1, a + 1, fun b hb ↦ (h b (by linarith)).trans ?_⟩
  refine mul_le_mul (le_max_left c 1) ?_ (by positivity) (by positivity)
  rw [abs_of_nonneg (by positivity)]
  exact (Real.rpow_le_rpow_of_exponent_le (mod_cast by linarith) (Nat.le_ceil C)).trans (by norm_num)

lemma bigO_const_pow_log_le_two_pow_log (A : ℝ) (C : ℕ) :
    ∃ C' : ℕ, (fun n ↦ A ^ (Nat.log2 n ^ C)) =O[.atTop] (fun n ↦ (2 : ℝ) ^ (Nat.log2 n ^ C')) := by
  use C + 1
  -- Let $k = \lceil \log_2 |A| \rceil$. Then $|A| \leq 2^k$.
  set k : ℕ := Nat.ceil (Real.logb 2 (|A|)) with hk;
  -- Then $|A|^{(\log n)^C} \leq (2^k)^{(\log n)^C} = 2^{k (\log n)^C}$.
  have h_bound : ∀ᶠ n in Filter.atTop, |A| ^ (Nat.log2 n) ^ C ≤ (2 : ℝ) ^ (k * (Nat.log2 n) ^ C) := by
    have h_bound : |A| ≤ (2 : ℝ) ^ k := by
      by_cases hA : A = 0;
      · norm_num [ hA ];
      · have := Nat.le_ceil ( Real.logb 2 |A| ) ; rw [ Real.logb_le_iff_le_rpow ] at this <;> norm_cast at * ; aesop;
    simpa only [ pow_mul ] using Filter.Eventually.of_forall fun n => pow_le_pow_left₀ ( abs_nonneg _ ) h_bound _;
  -- Since $k$ is a constant, we can choose $C' = C + 1$ such that $k (\log n)^C \leq (\log n)^{C+1}$ for sufficiently large $n$.
  have h_const : ∃ N : ℕ, ∀ n ≥ N, k * (Nat.log2 n) ^ C ≤ (Nat.log2 n) ^ (C + 1) := by
    use 2 ^ ( k + 1 );
    intro n hn
    rw [ pow_succ' ]
    gcongr
    rw [ Nat.le_log2 ]
    · exact le_trans ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) hn;
    · linarith [ Nat.pow_le_pow_right two_pos ( show k + 1 ≥ 1 by norm_num ) ];
  apply Asymptotics.IsBigO.of_bound 1
  simp +zetaDelta at *;
  exact ⟨ Nat.max h_bound.choose h_const.choose, fun n hn => le_trans ( h_bound.choose_spec n ( le_trans ( Nat.le_max_left _ _ ) hn ) ) ( pow_le_pow_right₀ ( by norm_num ) ( h_const.choose_spec n ( le_trans ( Nat.le_max_right _ _ ) hn ) ) ) ⟩

theorem quasipoly_iff_real_two_pow {f : ℕ → ℕ} : f ∈ quasipoly ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ 2 ^ (Nat.log2 n ^ C) : ℕ → ℝ) := by
  simp [quasipoly, Asymptotics.isBigO_iff, Norm.norm, Nat.log2_eq_log_two]

theorem quasipoly_iff_real_const_pow {f : ℕ → ℕ} : f ∈ quasipoly ↔
    ∃ A C, (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ A ^ (Nat.log2 n ^ C) : ℕ → ℝ) := by
  rw [quasipoly_iff_real_two_pow]
  use (⟨2, ·⟩)
  rintro ⟨A, C, hC⟩
  exact (bigO_const_pow_log_le_two_pow_log A C).imp (fun _ ↦ hC.trans)

theorem e_pow_iff_rexp {f : ℕ → ℕ} : f ∈ e_pow ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp x) := by
  -- By definition of ceiling, we know that for any natural number $n$, $\lceil \exp(n) \rceil$ is either $\exp(n)$ or $\exp(n) + 1$.
  have h_ceil : ∀ n : ℕ, ⌈(Real.exp n)⌉₊ ≤ 2 * (Real.exp n) := by
    intro n; linarith [ Nat.ceil_lt_add_one ( Real.exp_nonneg n ), Real.add_one_le_exp n ] ;
  generalize_proofs at *;
  -- Since $2$ is a constant, multiplying by it doesn't change the asymptotic behavior. Therefore, $f \in \text{bigO}(\lceil \exp(n) \rceil)$ if and only if $f \in \text{bigO}(\exp(n))$.
  have h_const_mul : ∀ (f : ℕ → ℕ), (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ⌈(Real.exp n)⌉₊ : ℕ → ℤ) ↔ (f · : ℕ → ℝ) =O[.atTop] (fun n ↦ Real.exp n : ℕ → ℝ) := by
    -- By combining the results from h_const_mul and h_ceil, we can conclude the equivalence.
    intros f
    constructor;
    · intro hf;
      rw [ Asymptotics.isBigO_iff' ] at *;
      simp +zetaDelta at *;
      obtain ⟨ c, hc, a, ha ⟩ := hf; exact ⟨ c * 2, mul_pos hc zero_lt_two, a, fun n hn => by nlinarith [ ha n hn, h_ceil n ] ⟩ ;
    · intro hf;
      rw [ Asymptotics.isBigO_iff ] at *;
      obtain ⟨ c, hc ⟩ := hf;
      norm_num [ Norm.norm ] at *;
      exact ⟨ c * 2, hc.choose, fun n hn => by nlinarith [ hc.choose_spec n hn, h_ceil n, Real.exp_pos n, Nat.le_ceil ( Real.exp n ) ] ⟩;
  exact h_const_mul f

theorem exp_iff_rpow {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ C ^ x : ℕ → ℝ) := by
  constructor;
  · rintro ⟨ C, hC ⟩;
    use C;
    convert hC;
    norm_num [ Asymptotics.isBigO_iff ];
  · -- If there exists a real number $C$ such that $f(n) = O(C^n)$, then there exists a natural number $n$ such that $f(n) = O(n^n)$.
    intro h
    obtain ⟨C, hC⟩ := h
    have h_nat : ∃ n : ℕ, (fun x => (f x : ℝ)) =O[Filter.atTop] (fun x => (n : ℝ) ^ x) := by
      use ⌈|C|⌉₊;
      refine' hC.trans _;
      rw [ Asymptotics.isBigO_iff ];
      norm_num;
      exact ⟨ 1, 0, fun n hn => by rw [ one_mul ] ; gcongr ; exact Nat.le_ceil _ ⟩;
    obtain ⟨ n, hn ⟩ := h_nat;
    -- Since $n$ is a natural number, we can use it directly as the exponent in the exponential growth rate.
    use n;
    rw [ Asymptotics.isBigO_iff' ] at *;
    aesop

theorem exp_iff_rexp_mul {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp (C * x) : ℕ → ℝ) := by
  rw [exp_iff_rpow];
  constructor <;> rintro ⟨ C, hC ⟩;
  · use Real.log ( |C| + 1 );
    refine' hC.trans _;
    rw [ Asymptotics.isBigO_iff ];
    simp +zetaDelta at *;
    exact ⟨ 1, 0, fun n hn => by rw [ Real.exp_mul, Real.exp_log ( by positivity ) ] ; norm_num; exact pow_le_pow_left₀ ( by positivity ) ( by linarith [ abs_nonneg C ] ) _ ⟩;
  · use Real.exp C;
    simpa [ Real.exp_mul ] using hC

end equivalent_defs

section closure

section mul

variable {f g : ℕ → ℕ}

theorem const_mul (hf : f ∈ const) (hg : g ∈ const) : (f * g) ∈ const := by
  rw [mul_comm]
  exact mul_const hg hf

--Remove
theorem log_mul_const (hf : f ∈ log) (hg : g ∈ const) : (f * g) ∈ log := by
  exact mul_const hf hg

theorem polylog_mul (hf : f ∈ polylog) (hg : g ∈ polylog) : (f * g) ∈ polylog := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

--Remove
theorem sqrt_mul_const (hf : f ∈ sqrt) (hg : g ∈ const) : (f * g) ∈ sqrt := by
  exact mul_const hf hg

--Remove
theorem sublinear_mul_const (hf : f ∈ sublinear) (hg : g ∈ const) : (f * g) ∈ sublinear := by
  exact mul_const hf hg

--Remove
theorem linear_mul_const (hf : f ∈ linear) (hg : g ∈ const) : (f * g) ∈ linear := by
  exact mul_const hf hg

theorem linear_of_sqrt_mul_sqrt (hf : f ∈ sqrt) (hg : g ∈ sqrt) : (f * g) ∈ linear := by
  convert (hf.mul hg).trans ?_
  rw [ Asymptotics.isBigO_iff' ]
  simp
  exact ⟨ 1, by norm_num, 0, fun b hb => by
    norm_cast; nlinarith [ Nat.sqrt_le b ] ⟩

--Remove
theorem linarithmic_mul_const (hf : f ∈ linarithmic) (hg : g ∈ const) : (f * g) ∈ linarithmic := by
  exact mul_const hf hg

theorem linarithmic_of_linear_mul_log (hf : f ∈ linear) (hg : g ∈ log) : (f * g) ∈ linarithmic := by
  exact Asymptotics.IsBigO.mul hf hg

theorem quasilinear_mul_polylog (hf : f ∈ quasilinear) (hg : g ∈ polylog) : (f * g) ∈ quasilinear := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add, mul_assoc]

theorem poly_mul (hf : f ∈ poly) (hg : g ∈ poly) : (f * g) ∈ poly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem quasipoly_mul (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : (f * g) ∈ quasipoly := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  simp [quasipoly]
  -- Let $C = a + b$. Then we have $(fun x => ((f x) * (g x)) : ℝ)$ is $O[Filter.atTop] ((fun n => (2 : ℝ) ^ ((Nat.log 2 n) ^ C) : ℕ → ℝ))$.
  use a + b
  convert (ha.mul hb).trans ?_
  norm_num [Asymptotics.isBigO_iff, Norm.norm]
  use 2, 2, fun k hk => ?_
  rw [← pow_succ', Nat.pow_add, ← pow_add]
  exact pow_le_pow_right₀ one_le_two ( by nlinarith [ pow_pos ( show Nat.log 2 k > 0 from Nat.log_pos ( by norm_num ) hk ) a, pow_pos ( show Nat.log 2 k > 0 from Nat.log_pos ( by norm_num ) hk ) b ] );

--Remove
theorem two_pow_mul_const (hf : f ∈ two_pow) (hg : g ∈ const) : (f * g) ∈ two_pow := by
  exact mul_const hf hg

--Remove
theorem e_pow_mul_const (hf : f ∈ e_pow) (hg : g ∈ const) : (f * g) ∈ e_pow := by
  exact mul_const hf hg

theorem e_pow_of_two_pow_mul_quasipoly (hf : f ∈ two_pow) (hg : g ∈ quasipoly) : (f * g) ∈ e_pow := by
  simp [e_pow, bigO, two_pow, quasipoly] at *
  simp [Asymptotics.isBigO_iff'] at hf hg
  simp [Asymptotics.isBigO_iff]
  obtain ⟨c₁, hc₁, k₁, h₁⟩ := hf
  obtain ⟨C, c₂, hc₂, k₂, h₂⟩ := hg
  use c₁
  suffices hs : ∃ k, ∀ b ≥ k, (2 ^ b) * (c₂ * 2 ^ Nat.log 2 b ^ C) ≤ ⌈Real.exp b⌉₊ by
    rcases hs with ⟨k, hk⟩
    use k ⊔ k₁ ⊔ k₂
    intro b hb
    specialize h₁ b ((le_max_right _ _).trans <| (le_max_left _ _).trans hb)
    specialize h₂ b ((le_max_right _ _).trans hb)
    specialize hk b ((le_max_left _ _).trans <| (le_max_left _ _).trans hb)
    simp only [norm, Int.cast_ofNat, Nat.abs_ofNat] at h₁ h₂
    trans (c₁ * 2 ^ b) * (c₂ * 2 ^ Nat.log 2 b ^ C)
    · gcongr
    · rw [mul_assoc]
      gcongr
  clear c₁ hc₁ k₁ h₁ k₂ h₂
  -- Simplifying the goal using properties of exponential functions and logs
  suffices h_exp_log : ∃ k : ℕ, ∀ b ≥ k, (c₂ * 2 ^ (b + (Nat.log 2 b) ^ C)) ≤ (Nat.ceil ((Real.exp b : ℝ))) by
    simpa only [ mul_assoc, mul_comm, mul_left_comm, pow_add ] using h_exp_log;
  suffices h_exp_log : ∃ k : ℕ, ∀ b ≥ k, (c₂ * 2 ^ (b + (Nat.log 2 b) ^ C)) ≤ (Real.exp b) by
    exact ⟨ h_exp_log.choose, fun n hn => by simpa only [ pow_add, mul_assoc ] using le_trans ( h_exp_log.choose_spec n hn ) ( Nat.le_ceil _ ) ⟩;
  -- By dividing both sides of the inequality by $2^b$, we reduce it to showing that $c₂ * 2 ^ ((log2 b) ^ C) ≤ \exp(b - b \cdot \log_2(e))$.
  suffices h₂ : ∃ k : ℕ, ∀ b ≥ k, (c₂ * 2 ^ ((Nat.log 2 b) ^ C)) ≤ (Real.exp (b * (1 - Real.log 2))) by
    rcases h₂ with ⟨k, hk⟩
    use k; intro b hb; rw [ pow_add ] ; rw [ ← mul_comm ] ; specialize hk b hb; convert mul_le_mul_of_nonneg_left hk <| pow_nonneg zero_le_two b using 1 ;
    · ring
    · rw [ mul_sub, mul_one, Real.exp_sub ];
      norm_num [ Real.exp_neg, Real.exp_nat_mul, Real.exp_log, mul_div_cancel₀ ];
  -- We'll use that exponential functions grow faster than polynomial functions. Specifically, we'll find a $k$ such that for all $b \geq k$, $2^{(\log_2(b))^C}$ is dominated by $e^{b (1 - \log(2))}$.
  suffices h_exp_poly : Filter.Tendsto (fun b : ℕ => (2 ^ ((Nat.log 2 b) ^ C) : ℝ) / Real.exp (b * (1 - Real.log 2))) Filter.atTop (nhds 0) by
    have := h_exp_poly.eventually ( gt_mem_nhds <| show 0 < c₂⁻¹ by positivity )
    rw [Filter.eventually_atTop] at this
    peel this with _ n _ this
    rw [ div_lt_iff₀ ( Real.exp_pos _ ) ] at this
    nlinarith [ Real.exp_pos ( n * ( 1 - Real.log 2 ) ), inv_mul_cancel₀ ( ne_of_gt hc₂ ) ]
  -- Let $y = \log_2(b)$, therefore the expression becomes $\lim_{y \to \infty} \frac{2^{y^C}}{e^{2^y (1 - \log(2))}}$.
  suffices h_log : Filter.Tendsto (fun y : ℕ => (2 ^ (y ^ C) : ℝ) / Real.exp (2 ^ y * (1 - Real.log 2))) Filter.atTop (nhds 0) by
    refine' squeeze_zero_norm' _ ( h_log.comp ( _ ) );
    case refine'_2 => use fun x => Nat.log 2 x;
    -- Case 1
    · simp only [norm_div, norm_pow, Real.norm_ofNat, Real.norm_eq_abs, Real.abs_exp, Function.comp_apply,
        Filter.eventually_atTop, ge_iff_le]
      refine' ⟨ 4, fun n hn => _ ⟩;
      gcongr;
      -- Case 1
      · linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
      -- Case 2
      · exact_mod_cast Nat.pow_log_le_self 2 <| by linarith;
    -- Case 2
    · rw [ Filter.tendsto_atTop_atTop ];
      exact fun b => ⟨ 2 ^ b, fun a ha => Nat.le_log_of_pow_le ( by norm_num ) ha ⟩;
  -- Taking the natural logarithm of the expression inside the limit, we get $\lim_{y \to \infty} (y^C \ln(2) - 2^y (1 - \ln(2)))$.
  suffices h_ln : Filter.Tendsto (fun y : ℕ => y ^ C * Real.log 2 - 2 ^ y * (1 - Real.log 2)) Filter.atTop Filter.atBot by
    -- If the natural logarithm of the expression tends to $-\infty$, then the expression tends to $0$.
    have h_exp_ln : Filter.Tendsto (fun y : ℕ => Real.exp (y ^ C * Real.log 2 - 2 ^ y * (1 - Real.log 2))) Filter.atTop (nhds 0) := by
      aesop;
    convert h_exp_ln using 1;
    norm_num [ Real.exp_sub, Real.exp_nat_mul, Real.exp_log ];
    exact funext fun x => by
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ]
      norm_num [mul_comm]
  -- We'll use that exponential functions grow faster than polynomial functions under the given conditions.
  have h_exp_poly : Filter.Tendsto (fun y : ℕ => (2 : ℝ) ^ y / y ^ C) Filter.atTop Filter.atTop := by
    -- Recognize that this is a special case of the exponential function $a^x / x^C$ where $a = 2$.
    suffices h_exp : Filter.Tendsto (fun x : ℝ => Real.exp (x * Real.log 2) / x ^ C) Filter.atTop Filter.atTop by
      convert h_exp.comp tendsto_natCast_atTop_atTop using 2 ; norm_num [ Real.exp_nat_mul, Real.exp_log ];
    -- Let $y = x \log 2$, therefore the limit becomes $\lim_{y \to \infty} \frac{e^y}{y^C}$.
    suffices h_limit_y : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ C) Filter.atTop Filter.atTop by
      have h_subst : Filter.Tendsto (fun x : ℝ => Real.exp (x * Real.log 2) / (x * Real.log 2) ^ C) Filter.atTop Filter.atTop := by
        exact h_limit_y.comp <| Filter.tendsto_id.atTop_mul_const <| Real.log_pos <| by norm_num;
      -- We simplify the expression $\frac{e^{x \ln 2}}{(x \ln 2)^C}$ to $\frac{e^{x \ln 2}}{x^C (\ln 2)^C}$.
      have h_simplify : Filter.Tendsto (fun x : ℝ => Real.exp (x * Real.log 2) / x ^ C / (Real.log 2) ^ C) Filter.atTop Filter.atTop := by
        simpa only [ mul_pow, div_div ] using h_subst;
      convert h_simplify.atTop_mul_const ( pow_pos ( Real.log_pos one_lt_two ) C ) using 2
      ring_nf
      norm_num [ mul_assoc, mul_comm, mul_left_comm ]
    exact Real.tendsto_exp_div_pow_atTop _;
  -- Rewrite the limit expression using the property of limits: $\lim_{y \to \infty} (y^C \ln(2) - 2^y (1 - \ln(2))) = \lim_{y \to \infty} y^C (\ln(2) - \frac{2^y (1 - \ln(2))}{y^C})$.
  have h_rewrite : Filter.Tendsto (fun y : ℕ => (y ^ C : ℝ) * (Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C)) Filter.atTop Filter.atBot := by
    -- Since $\frac{2^y (1 - \ln(2))}{y^C}$ tends to infinity, $\ln(2) - \frac{2^y (1 - \ln(2))}{y^C}$ tends to $-\infty$.
    have h_ln_tendsto : Filter.Tendsto (fun y : ℕ => Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C) Filter.atTop Filter.atBot := by
      -- Since $1 - \ln(2)$ is positive, multiplication by $(1 - \ln(2))$ preserves the limit.
      have h_mul : Filter.Tendsto (fun y : ℕ => (2 ^ y * (1 - Real.log 2)) / y ^ C) Filter.atTop Filter.atTop := by
        simpa only [ mul_div_right_comm ] using h_exp_poly.atTop_mul_const ( sub_pos.mpr <| Real.log_two_lt_d9.trans_le <| by norm_num );
      rw [ Filter.tendsto_atTop_atBot ];
      exact fun x => Filter.eventually_atTop.mp ( h_mul.eventually_gt_atTop ( Real.log 2 - x ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ by linarith [ hN n hn ] ⟩;
    rw [ Filter.tendsto_atTop_atBot ] at *;
    intro b;
    obtain ⟨ i, hi ⟩ := h_ln_tendsto ( Min.min b 0 );
    exact ⟨ i + 1, fun j hj => le_trans ( mul_le_mul_of_nonneg_left ( hi _ ( by linarith ) ) ( by positivity ) ) <|
      by nlinarith [ min_le_left b 0, min_le_right b 0,
        show ( j:ℝ ) ^ C ≥ 1 from one_le_pow₀ ( by norm_cast; linarith ) ] ⟩;
  refine' h_rewrite.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with y hy using (by
    rw [ mul_sub, mul_div_cancel₀ _ ( by positivity ) ] ))

theorem exp_mul (hf : f ∈ exp) (hg : g ∈ exp) : (f * g) ∈ exp := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a * b
  simp only [Nat.cast_mul, mul_pow]
  exact ha.mul hb

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
  refine fun _ h ↦ h.trans ?_
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun _ hn ↦ ?_⟩
  exact one_le_mul_of_one_le_of_one_le le_rfl (mod_cast Nat.le_log_of_pow_le one_lt_two hn)

theorem const_ssubset_log : const ⊂ log := by
  simp only [const, log, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset,
    Pi.one_apply, Nat.cast_one]
  use const_subset_log
  simp only [Asymptotics.isBigO_one_iff, Int.norm_natCast, not_forall]
  use Nat.log 2
  constructor
  · norm_num [ Filter.IsBoundedUnder, Filter.IsBounded ];
    intro x n;
    rcases exists_nat_gt x with ⟨k, hk⟩
    exact ⟨ 2 ^ ( n + k + 1 ), by linarith [( n + k + 1 ).lt_two_pow_self], by rw [ Nat.log_pow ( by norm_num ) ] ; push_cast; linarith ⟩
  · apply Asymptotics.isBigO_refl

theorem log_ssubset_polylog : log ⊂ polylog := by
  rw [log, polylog, ssubset_iff_subset_not_subset]
  constructor
  · intro f h
    use 1
    simp_rw [pow_one]
    convert h
  · simp only [bigO, Set.setOf_subset_setOf, forall_exists_index, not_forall]
    use fun n ↦ (Nat.log 2 n) ^ 2, 2, Asymptotics.isBigO_refl ..
    norm_num [Asymptotics.isBigO_iff]
    intro x y
    obtain ⟨n, hn⟩ := exists_nat_gt x
    use 2 ^ (y + n + 1)
    constructor
    · linarith [(y + n + 1).lt_two_pow_self]
    · norm_num [Nat.log_pow]
      nlinarith


theorem polylog_subset_sqrt : polylog ⊆ sqrt := by
  intros f hf
  rw [polylog] at hf
  obtain ⟨k, hk⟩ := hf;
  rw [ Asymptotics.isBigO_iff' ] at hk;
  rcases hk with ⟨ c, hc₀, hfc ⟩;
  -- Now consider the inequality $\|f x\| \leq c \| \log^k x \|$ for all sufficiently large $x$.
  obtain ⟨ N, hN ⟩ : ∃ N, ∀ x ≥ N, (f x : ℝ) ≤ c * Real.logb 2 x ^ k := by
    simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
    obtain ⟨w, h⟩ := hfc
    refine ⟨ w + 2, fun x hx ↦ le_trans ( h x <| by linarith ) ?_ ⟩;
    gcongr;
    have : Nat.log 2 x ≤ Real.logb 2 ( x:ℝ ) := by
      rw [ Real.le_logb_iff_rpow_le ( by norm_num ) ( by norm_cast; linarith ) ] ; norm_cast;
      rw [ ← Nat.le_log_iff_pow_le ] <;> linarith;
    exact this
  -- Show that $ c * \log^k x \leq \sqrt{x} $ for all sufficiently large $ x $.
  obtain ⟨ M, hM ⟩ : ∃ M, ∀ x ≥ M, c * Real.logb 2 x ^ k ≤ Real.sqrt x := by
    -- To prove the bound, we can use the fact that for large enough $x$, $(Real.logb 2 x) ^ k / \sqrt{x}$ tends to $0$.
    have h_limit : Filter.Tendsto (fun x : ℝ => (Real.logb 2 x) ^ k / Real.sqrt x) Filter.atTop (nhds 0) := by
      -- Let `y = log₂ x`, therefore the expression becomes `(y ^ k) / Real.sqrt (2 ^ y)`.
      suffices h_subst : Filter.Tendsto (fun y : ℝ => y ^ k / Real.sqrt (2 ^ y)) Filter.atTop (nhds 0) by
        exact (h_subst.comp ( Real.tendsto_logb_atTop one_lt_two)).congr' (by
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx
          simp [ Real.sqrt_eq_rpow, Real.rpow_logb, hx ] );
      -- We'll use the exponential property: $\sqrt{2^y} = 2^{y/2}$.
      suffices h_exp : Filter.Tendsto (fun y : ℝ => y ^ k / 2 ^ (y / 2)) Filter.atTop (nhds 0) by
        convert h_exp using 3
        rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by norm_num ) ]
        ring_nf
      -- Let `z = y / 2`, therefore the expression becomes `(2z)^k / e^{z * Real.log 2} = 2^k * z^k / e^{z * Real.log 2}`.
      suffices h_z : Filter.Tendsto (fun z : ℝ => (2 ^ k : ℝ) * z ^ k / Real.exp (z * Real.log 2)) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const <| show ( 2 : ℝ ) ⁻¹ > 0 by positivity ) using 2
        norm_num
        ring_nf
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
  -- Let $x \geq \max(N, M)$.
  obtain ⟨w_1, h_1⟩ : ∃ K, ∀ x ≥ K, f x ≤ Real.sqrt x :=
    ⟨⌈M⌉₊ + N, fun x hx => (hN x (by linarith)).trans
        ( by simpa using hM x (( Nat.le_ceil _ ).trans ( mod_cast by linarith ) ) ) ⟩
  simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
  apply Asymptotics.isBigO_iff.mpr
  use 1
  norm_num;
  exact ⟨ w_1 + 1, fun b hb => Nat.le_sqrt.mpr <| by
    specialize h_1 b (by bound)
    rw [ Real.le_sqrt ] at * <;> norm_cast at * <;> linarith ⟩

theorem polylog_ssubset_sqrt : polylog ⊂ sqrt := by
  use polylog_subset_sqrt
  simp only [polylog, sqrt, bigO, Set.setOf_subset_setOf]
  push_neg
  use Nat.sqrt, Asymptotics.isBigO_refl ..
  intro C
  apply Asymptotics.IsLittleO.not_isBigO
  · rw [ Asymptotics.isLittleO_iff ];
    intro c a
    simp_all only [Nat.cast_pow, norm_pow, norm_natCast, Filter.eventually_atTop, ge_iff_le]
    -- We'll use that logarithmic base 2 grows slower than any polynomial function, so that for large $n$, $\log_2(n)^C$ is much smaller than $n^{1/2}$.
    have h_log_growth : Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) ^ C / Real.sqrt n) Filter.atTop (nhds 0) := by
      -- We'll use that logarithmic base 2 grows slower than any polynomial function under the real numbers, so that for large $n$, $(\log_2(n))^C$ is much smaller than $\sqrt{n}$.
      have h_log_growth : Filter.Tendsto (fun x : ℝ => (Real.log x / Real.log 2) ^ C / Real.sqrt x) Filter.atTop (nhds 0) := by
        -- Let $y = \log_2(x)$. Then we can rewrite our limit in terms of $y$:
        suffices h_log_growth_y : Filter.Tendsto (fun y : ℝ => y ^ C / Real.sqrt (2 ^ y)) Filter.atTop (nhds 0) by
          have := h_log_growth_y.comp ( Real.tendsto_log_atTop.const_mul_atTop ( by positivity : ( 0 : ℝ ) < ( Real.log 2 ) ⁻¹ ) );
          refine this.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx;
          -- By simplifying, we can see that the two functions are equal.
          field_simp [hx];
          norm_num +zetaDelta at *;
          -- Simplify the denominator: $\sqrt{2^{(\log x) / \log 2}} = \sqrt{x}$.
          field_simp [Real.sqrt_eq_rpow];
          erw [ Real.rpow_logb ] <;> linarith
        -- Notice that $\sqrt{2^y} = 2^{y/2}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{y^C}{2^{y/2}}$.
        suffices h_log_growth_y_simplified : Filter.Tendsto (fun y : ℝ => y ^ C / Real.exp (y * Real.log 2 / 2)) Filter.atTop (nhds 0) by
          convert h_log_growth_y_simplified using 2 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ] ;
          ring_nf
          rw [ ← Real.exp_mul ];
        -- Let $z = \frac{y \log 2}{2}$, so we can rewrite the limit as $\lim_{z \to \infty} \frac{(\frac{2z}{\log 2})^C}{e^z}$.
        suffices h_log_growth_z : Filter.Tendsto (fun z : ℝ => ((2 * z) / Real.log 2) ^ C / Real.exp z) Filter.atTop (nhds 0) by
          have h_log_growth_z : Filter.Tendsto (fun y : ℝ => ((2 * (y * Real.log 2 / 2)) / Real.log 2) ^ C / Real.exp (y * Real.log 2 / 2)) Filter.atTop (nhds 0) := by
            exact h_log_growth_z.comp ( Filter.Tendsto.atTop_mul_const ( by positivity ) <| Filter.tendsto_id.atTop_mul_const <| by positivity );
          convert h_log_growth_z using 3 ;
          ring_nf
          norm_num
        -- Now consider the term $(\frac{2z}{\log 2})^C / e^z$. We want to show that this goes to $0$ as $z \to \infty$.
        suffices h_term : Filter.Tendsto (fun z : ℝ => z ^ C / Real.exp z) Filter.atTop (nhds 0) by
          convert h_term.const_mul ( ( Real.log 2 ) ⁻¹ ^ C * 2 ^ C ) using 2 <;> ring;
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C;
      refine' squeeze_zero_norm' _ ( h_log_growth.comp tendsto_natCast_atTop_atTop );
      refine' Filter.eventually_atTop.mpr ⟨ 2, fun n hn => _ ⟩ ; rw [ Function.comp_apply, Real.norm_of_nonneg ( by positivity ) ] ; gcongr;
      rw [ le_div_iff₀ ( Real.log_pos one_lt_two ), ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) <| by norm_cast ; exact Nat.pow_log_le_self _ <| by positivity;
    have this := h_log_growth.eventually ( gt_mem_nhds <| show 0 < c / 2 by positivity ) ;
    rw [Filter.eventually_atTop] at this
    obtain ⟨w, h⟩ := this
    refine ⟨w + 4, fun n hn ↦ ?_⟩
    specialize h n ( by linarith )
    rw [ div_lt_iff₀ ( by norm_num; linarith ) ] at h;
    refine le_trans ( le_of_lt h ) ?_;
    nlinarith only [ a,
      show ( Nat.sqrt n:ℝ ) ≥ 1 from Nat.one_le_cast.2 ( n.sqrt_pos.2 ( by linarith ) ),
      show ( √n:ℝ ) ≤ Nat.sqrt n + 1 from Real.sqrt_le_iff.2 ⟨by positivity, by norm_cast; nlinarith [ Nat.lt_succ_sqrt n ] ⟩]
  · rw [Filter.frequently_atTop]
    exact (⟨· + 2, by simp⟩)

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
  simp
  nlinarith [ show ( Nat.sqrt b :ℝ ) ≤ Real.sqrt ↑b by exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' b, Real.sq_sqrt <| Nat.cast_nonneg b ]

theorem sqrt_ssubset_sublinear : sqrt ⊂ sublinear := by
  use sqrt_subset_sublinear
  simp only [sqrt, sublinear, bigO]
  norm_num [ GrowthRate.littleO ];
  -- Consider the function $f(n) = \sqrt{n} \log(n)$.
  use fun n => Nat.sqrt n * Nat.log 2 n;
  simp_all only [Nat.cast_mul]
  apply And.intro
  · refine' Asymptotics.isLittleO_iff.2 fun ε hε => _;
    -- We'll use that $\log_2 x$ grows slower than any polynomial function, specifically $x^{1/2}$.
    have h_log_growth : Filter.Tendsto (fun x : ℕ => (Nat.log 2 x : ℝ) / Real.sqrt x) Filter.atTop (nhds 0) := by
      -- We can use the change of variables $u = \log_2 x$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => u / 2^(u/2)) Filter.atTop (nhds 0) by
        have h_log : Filter.Tendsto (fun x : ℕ => (Nat.log 2 x : ℝ) / 2^(Nat.log 2 x / 2 : ℝ)) Filter.atTop (nhds 0) := by
          exact h_log.comp ( tendsto_natCast_atTop_atTop.comp ( Filter.tendsto_atTop_atTop.mpr fun n => ⟨ 2 ^ n, fun x hx => Nat.le_log_of_pow_le ( by norm_num ) hx ⟩ ) );
        refine' squeeze_zero_norm' _ h_log
        simp_all only [norm_div, RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop, ge_iff_le]
        refine' ⟨ 2, fun n hn => _ ⟩ ; rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; gcongr;
        rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> norm_num;
        · have := Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 2 ^ Nat.log 2 n by exact_mod_cast Nat.pow_log_le_self 2 ( by positivity ) ) ; norm_num at * ; nlinarith [ Real.log_pos one_lt_two ];
        · linarith;
      -- We can use the fact that $2^{u/2} = e^{u \ln 2 / 2}$ and apply the exponential function to both the numerator and the denominator.
      suffices h_exp : Filter.Tendsto (fun u : ℝ => u / Real.exp (u * Real.log 2 / 2)) Filter.atTop (nhds 0) by
        convert h_exp using 2 ; norm_num [ Real.rpow_def_of_pos ]
        ring_nf
      -- Let $y = \frac{u \ln 2}{2}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{2y}{e^y}$.
      suffices h_y : Filter.Tendsto (fun y : ℝ => 2 * y / Real.exp y) Filter.atTop (nhds 0) by
        have := h_y.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < Real.log 2 / 2 by positivity ) );
        convert this.div_const ( Real.log 2 ) using 2 <;> norm_num
        ring_nf
        norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      simpa [ mul_div_assoc, Real.exp_neg ] using Filter.Tendsto.const_mul 2 ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
    have := h_log_growth.eventually ( gt_mem_nhds <| show 0 < ε by positivity )
    simp_all only [Filter.eventually_atTop, ge_iff_le, norm_mul, norm_natCast]
    obtain ⟨w, h⟩ := this
    refine' ⟨ w + 1, fun n hn => _ ⟩
    have := h n ( by linarith ) ;
    rw [ div_lt_iff₀ ] at this
    · nlinarith [ show ( Nat.sqrt n : ℝ ) ≤ Real.sqrt n from Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' n,
        Real.mul_self_sqrt <| Nat.cast_nonneg n,
        show ( Nat.log 2 n : ℝ ) ≥ 0 by positivity ]
    · norm_num at *
      linarith;
  · intro a
    contrapose! a;
    rw [ Asymptotics.isBigO_iff ]
    simp_all
    intro x x_1
    -- We'll use that logarithmic growth is faster than any polynomial growth.
    have h_log_growth : Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) - x) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_add_const_right _ _ ( tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun n => ⟨ 2 ^ n, fun m hm => Nat.le_log_of_pow_le ( by norm_num ) hm ⟩ );
    have := h_log_growth.eventually_gt_atTop 0;
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ x_1 + N + 1, by linarith, by nlinarith [ hN ( x_1 + N + 1 ) ( by linarith ), show ( Nat.sqrt ( x_1 + N + 1 ) : ℝ ) ≥ 1 by exact_mod_cast Nat.sqrt_pos.mpr ( by linarith ) ] ⟩ ;


theorem sublinear_ssubset_linear : sublinear ⊂ linear := by
  simp only [littleO, linear, bigO, Set.setOf_subset_setOf, ssubset_iff_subset_not_subset]
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
  · linarith [(k + n).lt_two_pow_self]
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
  simp [quasilinear, poly]
  intro f C h
  use C + 1
  apply h.trans
  norm_num [ Asymptotics.isBigO_iff ];
  refine' ⟨ 1, 2, fun n hn => _ ⟩ ; norm_num;
  -- We can cancel $n$ since it is positive and simplify the inequality to $\log_2(n)^C \leq n^C$.
  suffices h_cancel : (Nat.log 2 n : ℝ) ^ C ≤ (n : ℝ) ^ C by
    simpa [ pow_succ' ] using mul_le_mul_of_nonneg_left h_cancel <| Nat.cast_nonneg _;
  gcongr
  exact (Nat.log_lt_of_lt_pow (by linarith) (by linarith [n.lt_two_pow_self])).le

theorem quasilinear_ssubset_poly : quasilinear ⊂ poly := by
  use quasilinear_subset_poly
  simp only [quasilinear, poly, Set.setOf_subset_setOf, not_forall, exists_prop]
  use (· ^ 2)
  constructor
  · use 2
    simpa using Asymptotics.isBigO_refl _ _
  · norm_num [ Asymptotics.isBigO_iff' ];
    intro x y hy z;
    -- We'll use that exponential functions grow faster than polynomial functions.
    have h_exp_poly : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (Nat.log 2 n : ℝ) ^ x / (n : ℝ) ^ 2) Filter.atTop (nhds 0) := by
      -- We can simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) ^ x / (n : ℝ)) Filter.atTop (nhds 0) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ div_eq_div_iff ] <;> ring_nf <;> positivity );
      -- Let $y = \log_2 n$, therefore the expression becomes $\frac{y^x}{2^y}$.
      suffices h_log : Filter.Tendsto (fun y : ℕ => (y : ℝ) ^ x / (2 ^ y)) Filter.atTop (nhds 0) by
        have h_subst : Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) ^ x / (2 ^ (Nat.log 2 n))) Filter.atTop (nhds 0) := by
          exact h_log.comp ( Filter.tendsto_atTop_atTop.mpr fun n => ⟨ 2 ^ n, fun m hm => Nat.le_log_of_pow_le ( by norm_num ) hm ⟩ );
        refine' squeeze_zero_norm' _ h_subst;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn
        rw [ Real.norm_of_nonneg ( by positivity ) ]
        gcongr
        norm_cast
        exact Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hn)
      -- We can convert this limit into a form that is easier to handle by substituting $z = y \log 2$.
      suffices h_log : Filter.Tendsto (fun z : ℝ => z ^ x / Real.exp z) Filter.atTop (nhds 0) by
        have := h_log.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos one_lt_two ) );
        convert this.div_const ( Real.log 2 ^ x ) using 2 <;> norm_num [ Real.exp_nat_mul, Real.exp_log ]
        ring_nf
        norm_num [ ne_of_gt, Real.log_pos ];
      simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero x;
    have := h_exp_poly.eventually ( gt_mem_nhds <| show 0 < y⁻¹ by positivity );
    simp at this
    obtain ⟨ N, hN ⟩ := this;
    exact ⟨ N + z + 1, by linarith, by have := hN ( N + z + 1 ) ( by linarith ) ; rw [ div_lt_iff₀ ( by positivity ) ] at this; nlinarith [ inv_mul_cancel₀ hy.ne', pow_pos ( by positivity : 0 < ( N + z + 1 : ℝ ) ) 2 ] ⟩ ;

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
  simp [poly, quasipoly]
  use fun n ↦ 2 ^ (Nat.log 2 n) ^ 2
  constructor
  · use 2
    exact_mod_cast Asymptotics.isBigO_refl ..
  · intro k hk;
    rw [ Asymptotics.isBigO_iff' ] at hk;
    norm_num +zetaDelta at *;
    obtain ⟨ c, hc₀, a, ha ⟩ := hk;
    -- Choose $b = 2^m$ for some $m$ large enough such that $2^{m^2} > c \cdot (2^m)^k$.
    obtain ⟨ m, hm ⟩ : ∃ m : ℕ, m > a ∧ 2 ^ (m ^ 2) > c * (2 ^ m) ^ k := by
      -- We can choose $m$ large enough such that $2^{m^2} > c \cdot 2^{mk}$ by taking $m$ such that $m^2 > mk + \log_2(c)$.
      have hm_exists : ∃ m : ℕ, m > a ∧ m^2 > m * k + Real.logb 2 c := by
        exact ⟨ a + k + ⌊Real.logb 2 c⌋₊ + 1, by linarith, by push_cast; nlinarith [ Nat.lt_floor_add_one ( Real.logb 2 c ) ] ⟩;
      obtain ⟨ m, hm₁, hm₂ ⟩ := hm_exists;
      use m;
      rw [ gt_iff_lt, Real.logb ] at hm₂;
      rw [ add_div', div_lt_iff₀ ] at hm₂ <;> norm_num at *;
      · exact ⟨ hm₁, by rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] ; norm_num; linarith ⟩;
      · positivity;
    specialize ha ( 2 ^ m ) ( Nat.le_of_lt ( Nat.lt_of_lt_of_le hm.1 ( Nat.le_of_lt ( Nat.recOn m ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; linarith ) ) ) )
    norm_num [ Norm.norm ] at ha
    exact ha.not_gt <| mod_cast hm.2

theorem quasipoly_subset_two_pow : quasipoly ⊆ two_pow := by
  rintro f ⟨ C, hC ⟩;
  have h_exp : (fun n => 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ) =O[Filter.atTop] (fun n => 2 ^ n : ℕ → ℤ) := by
    have h_exp : ∀ᶠ n in Filter.atTop, (Nat.log 2 n ^ C : ℕ) ≤ n := by
      have h_log : Filter.Tendsto (fun n => (Nat.log 2 n : ℝ) ^ C / n) Filter.atTop (nhds 0) := by
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$.
        suffices h_log_growth : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ C / (2 ^ m : ℝ)) Filter.atTop (nhds 0) by
          have h_log_growth : Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) ^ C / (2 ^ (Nat.log 2 n) : ℝ)) Filter.atTop (nhds 0) := by
            exact h_log_growth.comp ( Filter.tendsto_atTop_atTop.mpr fun m => ⟨ 2 ^ m, fun n hn => Nat.le_log_of_pow_le ( by norm_num ) hn ⟩ );
          refine' squeeze_zero_norm' _ h_log_growth;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn
          rw [ Real.norm_of_nonneg ( by positivity ) ]
          gcongr
          norm_cast
          exact Nat.pow_log_le_self 2 hn.ne'
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$ and using the fact that $2^m$ grows exponentially.
        suffices h_log_growth : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) by
          simpa [ Real.exp_nat_mul, Real.exp_log ] using h_log_growth;
        -- Let $y = m \log 2$, therefore the limit becomes $\lim_{y \to \infty} \frac{y^C}{e^y}$.
        suffices h_log_growth : Filter.Tendsto (fun y : ℝ => y ^ C / Real.exp y) Filter.atTop (nhds 0) by
          have h_log_growth : Filter.Tendsto (fun m : ℕ => (m * Real.log 2 : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) := by
            exact h_log_growth.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos one_lt_two;
          convert h_log_growth.div_const ( Real.log 2 ^ C ) using 2 <;> ring_nf
          norm_num [ Real.exp_ne_zero ] ;
          exact eq_div_of_mul_eq ( by positivity ) ( by ring );
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C;
      filter_upwards [ h_log.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ div_lt_one ( by positivity ) ] at hn; exact_mod_cast hn.le;
    rw [ Asymptotics.isBigO_iff ];
    norm_num +zetaDelta at *;
    exact ⟨ 1, h_exp.choose, fun n hn => by rw [ one_mul ] ; exact pow_le_pow_right₀ ( by norm_num [ Norm.norm ] ) ( h_exp.choose_spec n hn ) ⟩;
  -- By transitivity of big-O, if $f$ is $O(2^{Nat.log 2 n^C})$ and $2^{Nat.log 2 n^C}$ i
  -- $O(2^n)$, then $f$ is $O(2^n)$.
  simp [GrowthRate.two_pow];
  unfold GrowthRate.bigO
  simpa using hC.trans h_exp

theorem quasipoly_ssubset_two_pow : quasipoly ⊂ two_pow := by
  use quasipoly_subset_two_pow
  simp only [quasipoly, bigO, two_pow, Nat.cast_pow, Nat.cast_ofNat, Set.setOf_subset_setOf, not_forall, exists_prop]
  use (2 ^ ·), mod_cast Asymptotics.isBigO_refl ..
  -- Assume for contradiction that there exists a constant $C$ such that $2^n = O(2^{(\log n)^C})$.
  by_contra h_contra
  obtain ⟨C, hC⟩ := h_contra;
  -- We'll use that exponential functions grow faster than any polynomial function.
  have h_exp_growth : Filter.Tendsto (fun n => (2 : ℝ) ^ (Nat.log 2 n ^ C) / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    -- We can rewrite the limit expression using the properties of exponents: $2^{(\log n)^C} / 2^n = 2^{(\log n)^C - n}$.
    suffices h_exp : Filter.Tendsto (fun n => (2 : ℝ) ^ ((Nat.log 2 n) ^ C - n : ℝ)) Filter.atTop (nhds 0) by
      convert h_exp using 2 ; norm_num [ Real.rpow_sub ];
      norm_cast;
    -- We'll use that $(\log n)^C - n$ tends to $-\infty$ as $n$ tends to $\infty$.
    have h_log : Filter.Tendsto (fun n => (Nat.log 2 n : ℝ) ^ C - n) Filter.atTop Filter.atBot := by
      -- We'll use that $(\log n)^C$ grows much slower than $n$.
      have h_log_growth : Filter.Tendsto (fun n => (Nat.log 2 n : ℝ) ^ C / n) Filter.atTop (nhds 0) := by
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$.
        suffices h_log : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ C / (2 ^ m)) Filter.atTop (nhds 0) by
          have h_log : Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) ^ C / (2 ^ (Nat.log 2 n))) Filter.atTop (nhds 0) := by
            exact h_log.comp ( Filter.tendsto_atTop_atTop.mpr fun m => ⟨ 2 ^ m, fun n hn => Nat.le_log_of_pow_le ( by norm_num ) hn ⟩ );
          refine' squeeze_zero_norm' _ h_log;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; norm_cast ; exact Nat.pow_log_le_self 2 hn.ne';
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$. We'll use the fact that $2^m$ grows much faster than $m^C$.
        have h_log : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) := by
          -- Let $y = m \log 2$, therefore the limit becomes $\lim_{y \to \infty} \frac{y^C}{e^y}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ C / Real.exp y) Filter.atTop (nhds 0) by
            have h_subst : Filter.Tendsto (fun m : ℕ => (m * Real.log 2 : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) := by
              exact h_log.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos one_lt_two;
            convert h_subst.div_const ( Real.log 2 ^ C ) using 2
            · ring_nf
              norm_num [ mul_right_comm, mul_assoc, mul_left_comm, ne_of_gt, Real.log_pos ];
            · simp
          simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C;
        simpa [ Real.exp_nat_mul, Real.exp_log ] using h_log;
      -- We can rewrite the limit expression using the properties of limits.
      have h_rewrite : Filter.Tendsto (fun n => ((Nat.log 2 n : ℝ) ^ C / n - 1) * n) Filter.atTop Filter.atBot := by
        apply Filter.Tendsto.neg_mul_atTop;
        exacts [ show ( -1 : ℝ ) < 0 by norm_num, by simpa using h_log_growth.sub_const 1, tendsto_natCast_atTop_atTop ];
      refine h_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ sub_mul, div_mul_cancel₀ _ ( by positivity ) ] ; ring );
    norm_num [ Real.rpow_def_of_pos ];
    exact Filter.Tendsto.const_mul_atBot ( by positivity ) h_log;
  rw [ Asymptotics.isBigO_iff ] at hC;
  simp +zetaDelta at *;
  obtain ⟨ c, a, hc ⟩ := hC;
  -- Dividing both sides of the inequality by $2^b$, we get $1 \leq c \cdot \frac{2^{Nat.log 2 b^C}}{2^b}$.
  have h_div : ∀ b ≥ a, 1 ≤ c * (2 : ℝ) ^ (Nat.log 2 b ^ C) / (2 : ℝ) ^ b := by
    intro b hb; have := hc b hb; rw [ le_div_iff₀ ( by positivity ) ] ; norm_num [ Norm.norm ] at * ; linarith;
  exact absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds ( h_exp_growth.const_mul c ) <| Filter.eventually_atTop.mpr ⟨ a, fun n hn => by simpa [ mul_div_assoc ] using h_div n hn ⟩ ) ( by norm_num )

theorem two_pow_subset_e_pow : two_pow ⊆ e_pow := by
  -- We'll use the fact that $e \approx 2.718$ to show that $2^n$ is bounded above by $e^n$.
  have h_exp_bound : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (Real.exp n) := by
    intro n;
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
    exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( Real.log_two_lt_d9.le.trans ( by norm_num ) );
  -- By definition of big O, if $2^n \leq e^n$ for all $n$, then $2^n$ is $O(e^n)$.
  have h_two_pow_e_pow : (2 ^ · : ℕ → ℕ) ∈ bigO (fun n => ⌈Real.exp n⌉₊ : ℕ → ℕ) := by
    refine' Asymptotics.isBigO_iff.mpr _;
    -- Choose $c = 1$.
    use 1;
    exact Filter.eventually_atTop.mpr ⟨ 0, fun n hn => by erw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; exact_mod_cast Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( Real.exp n ), h_exp_bound n ] ⟩;
  -- Since `two_pow` is defined as `bigO (fun n => 2 ^ n)`, and we have shown that `(fun n => 2 ^ n) ∈ bigO (fun n => ⌈Real.exp n⌉₊)`, it follows that `two_pow ⊆ e_pow`.
  convert h_two_pow_e_pow using 1;
  constructor <;> intro h <;> unfold GrowthRate.two_pow GrowthRate.e_pow at * ; aesop;
  intro f hf;
  refine' hf.trans h

theorem two_pow_ssubset_e_pow : two_pow ⊂ e_pow := by
  use two_pow_subset_e_pow
  simp only [e_pow, bigO, two_pow, Nat.cast_pow, Nat.cast_ofNat, Set.setOf_subset_setOf, not_forall, exists_prop]
  use (⌈Real.exp ·⌉₊), Asymptotics.isBigO_refl ..
  rw [ Asymptotics.isBigO_iff' ];
  norm_num [ Norm.norm ];
  -- We'll use that exponential functions grow faster than linear functions.
  have h_exp_growth : Filter.Tendsto (fun n : ℕ => (Real.exp n : ℝ) / 2 ^ n) Filter.atTop Filter.atTop := by
    -- We can rewrite the limit expression using the fact that $e^n / 2^n = (e/2)^n$.
    suffices h_exp_growth : Filter.Tendsto (fun n : ℕ => (Real.exp 1 / 2 : ℝ) ^ n) Filter.atTop Filter.atTop by
      simpa [ Real.exp_nat_mul, div_pow ] using h_exp_growth;
    exact tendsto_pow_atTop_atTop_of_one_lt ( by have := Real.exp_one_gt_d9.le; norm_num1 at *; linarith );
  intro x hx n;
  have := h_exp_growth.eventually_gt_atTop ( x + 1 );
  exact Filter.eventually_atTop.mp ( this.and ( Filter.eventually_ge_atTop n ) ) |> fun ⟨ m, hm ⟩ ↦ ⟨ m, hm m ( by norm_num ) |>.2, by have := hm m ( by norm_num ) |>.1; rw [ lt_div_iff₀ ( by positivity ) ] at this; nlinarith [ Nat.le_ceil ( Real.exp m ), show ( 2 : ℝ ) ^ m > 0 by positivity ] ⟩

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
  simp [primitiveRecursive, bigO]
  constructor
  · use fun x ↦ ack x x
    constructor
    · exact Computable.comp computable₂_ack (Computable.id.pair Computable.id)
    · exact Asymptotics.isBigO_refl ..
  · intro x hx
    rw [Asymptotics.isBigO_iff']
    -- Since ack n n grows faster than any primrec, for any constant c,
    -- there exists an n such that ack n n > c * x n.
    have h_ineq : ∀ c > 0, ∃ N, ∀ n ≥ N, ack n n > c * x n := by
      intro c hc_pos
      -- There exists an m such that ack(m, n) > c * x(n) for all n.
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, ack m n > c * x n := by
        apply exists_lt_ack_of_nat_primrec
        suffices h_poly : Nat.Primrec (fun n => c * n) by
          exact h_poly.comp hx
        convert Nat.Primrec.mul.comp ((Nat.Primrec.const c).pair Nat.Primrec.id) using 2
        norm_num [Nat.unpaired]
      exact ⟨m, fun n hn => by simpa using (hm n).trans_le (ack_le_ack hn le_rfl)⟩
    simp only [norm_natCast, Filter.eventually_atTop, not_exists, not_and, not_forall, not_le]
    intro c hc n
    obtain ⟨N, hN⟩ := h_ineq (⌈c⌉₊) (Nat.ceil_pos.mpr hc)
    use n + N, by omega
    grw [Nat.le_ceil c]
    exact_mod_cast hN _ (by omega)

end ordering

end GrowthRate
