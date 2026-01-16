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

section defs

def bigO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =O[.atTop] (g · : ℕ → ℤ)

def littleO (g : ℕ → ℕ) : GrowthRate :=
  setOf <| fun f ↦ (f · : ℕ → ℤ) =o[.atTop] (g · : ℕ → ℤ)

--Defining the rate classes, sorted in order of growing more quickly.
--Summary:

/-
const       := bigO 1
log         := bigO (Nat.log 2)
polylog     := setOf ...
sqrt        := bigO Nat.sqrt
sublinear   := setOf ...
linear      := bigO id
linearithmic := bigO (fun n ↦ n * Nat.log 2 n)
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

/-- linearithmic growth rates: `O(n * log n)` -/
abbrev linearithmic := bigO (fun n ↦ n * Nat.log 2 n)

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
    exact ⟨ Finset.sup ( Finset.range w_1 ) f, fun n hn ↦ Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
  exact ⟨ ⌈w⌉₊ + M, fun n ↦ if hn : n < w_1 then le_trans ( hM n hn ) ( Nat.le_add_left _ _ ) else le_trans ( Nat.cast_le.mp ( le_trans ( h_1 n ( le_of_not_gt hn ) ) ( Nat.le_ceil _ ) ) ) ( Nat.le_add_right _ _ ) ⟩

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
  exact ⟨x ⊔ y, w ⊔ w_1, fun k hk ↦ by
    rw [ abs_of_nonneg ( by positivity : ( f k : ℝ ) + g k ≥ 0 ), abs_of_nonneg ( by positivity : ( a k + b k : ℝ ) ≥ 0 ) ]
    nlinarith [ h k ( le_of_max_le_left hk ), h_1 k ( le_of_max_le_right hk ), le_max_left x y, le_max_right x y ] ⟩

end basic

section lawful

/-- We call a `GrowthRate` *lawful* if it is closed under dominating sequences, addition, and
composition with a sublinear function; and is nontrivial (it contains at least one function besides
zero).

This last condition is equivalent to containing the constant function 1; or, containing any
two distinct functions. These conditions are enough to get most desirable properties. For instance,
all big-O and little-O rates are lawful, as is `poly`. -/
class LawfulGrowthRate (S : GrowthRate) : Prop where
  /-- If a function `f` is in S and it dominates `g` (is eventually greater than g), then `g ∈ S`. -/
  mem_dominating {f g : ℕ → ℕ} : (∀ᶠ x in .atTop, g x ≤ f x) → (f ∈ S) → g ∈ S
  /-- S is closed under addition. -/
  mem_add {f g : ℕ → ℕ} : (f ∈ S) → (g ∈ S) → (f + g ∈ S)
  /-- If a function `f` is in S and `g` is sublinear, then `f ∘ g ∈ S`. -/
  comp_le_id {f g : ℕ → ℕ} (hf : f ∈ S) (hg : g ≤ id) : f ∘ g ∈ S
  /-- S contains the constant function 1. -/
  one_mem : 1 ∈ S

alias mem_dominating := LawfulGrowthRate.mem_dominating
alias add := LawfulGrowthRate.mem_add
alias comp_le_id' := LawfulGrowthRate.comp_le_id
alias one_mem := LawfulGrowthRate.one_mem

variable {f g : ℕ → ℕ} {S : GrowthRate} [LawfulGrowthRate S]

theorem comp_le_id (hf : f ∈ S) (hg : ∀ x, g x ≤ x) : f ∘ g ∈ S :=
  comp_le_id' hf hg

theorem mono (hf : f ∈ S) (hg : g ≤ f) : g ∈ S :=
  mem_dominating (.of_forall hg) hf

instance : Nonempty S :=
  ⟨1, one_mem (S := S)⟩

theorem zero_mem : 0 ∈ S := by
  obtain ⟨f, hf⟩ := Classical.inhabited_of_nonempty (α := S) inferInstance
  convert mem_dominating _ hf
  exact Filter.Eventually.of_forall fun _ ↦ Nat.zero_le _

instance : Nontrivial S :=
  ⟨⟨0, zero_mem⟩, ⟨1, one_mem⟩, by simp⟩

theorem const_mem (hf : f ∈ const) : f ∈ S := by
  obtain ⟨C, hC⟩ := bounded_of_const hf
  have h_C_one : (fun n ↦ C * 1) ∈ S := by
    have h_C_one (k : ℕ) : k • 1 ∈ S := by
      induction k
      · exact mem_dominating (by norm_num) one_mem
      · rename_i ih
        simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at ih ⊢
        exact add ih one_mem
    exact h_C_one C
  exact mem_dominating (by simp [hC]) h_C_one

theorem sub (hf : f ∈ S) (g) : f - g ∈ S := by
  apply mem_dominating ?_ hf
  rw [Filter.eventually_atTop]
  exact ⟨0, fun _ _ ↦ (Nat.cast_le.mpr <| Nat.sub_le ..)⟩

theorem mul_const (hf : f ∈ S) (hg : g ∈ const) : (f * g) ∈ S := by
  have ⟨C, hC⟩ := bounded_of_const hg
  apply mem_dominating (f := C * f)
  · rw [Filter.eventually_atTop]
    exact ⟨0, fun n hn ↦ by simp; grw [← hC n, mul_comm]⟩
  · clear hC
    induction C <;> simp [zero_mem, add_mul, add, *]

theorem const_mul (hf : f ∈ const) (hg : g ∈ S) : (f * g) ∈ S := by
  rw [mul_comm]
  exact mul_const hg hf

/-- If `f` has growth rate `S` and `g` has growth rate `sublinear`, then `f ∘ g` has growth rate `S`.
With the written assumptions on `LawfulGrowthRate`, this is doesn't hold if we use `linear` instead
of `sublinear`. Consider the case `S := O(2^n)` and `g := 2n`. Then `2^(2n) = 4^n` which is not in
 `O(2^n)`. -/
theorem comp_sublinear (hf : f ∈ S) (hg : g ∈ sublinear) : f ∘ g ∈ S := by
  -- By definition of sublinear, we have `g ∈ littleO id`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, g n ≤ n := by
    simpa using hg.def (c := 1) (by norm_num)
  apply mem_dominating (f := f ∘ (fun n => if n ≥ N then g n else n))
  · filter_upwards [ Filter.eventually_ge_atTop N ] with n hn
    aesop
  · apply comp_le_id' hf
    change ∀ n, (if n ≥ N then g n else n) ≤ n
    aesop

theorem comp_sub_nat (hf : f ∈ S) (k : ℕ) : (fun n ↦ f (n - k)) ∈ S :=
  comp_le_id hf (by simp)

theorem comp_eventually_le_id (hf : f ∈ S) (hg : ∀ᶠ x in .atTop, g x ≤ x) : f ∘ g ∈ S := by
  apply mem_dominating (f := f ∘ (fun x => min (g x) x))
  · filter_upwards [ hg ] with x hx
    aesop
  · exact comp_le_id' hf (fun x => min_le_right _ _);

theorem comp_const (f) (hg : g ∈ const) : f ∘ g ∈ const := by
  -- Since $g \in \text{const}$, there exists a constant $C$ such that $g(n) \leq C$ for all $n$.
  obtain ⟨C, hC⟩ := bounded_of_const hg;
  -- Since $f \circ g$ is bounded by the maximum value of $f$ over the range of $g$, and $g$ is bounded, $f \circ g$ is also bounded. Therefore, $f \circ g \in \text{const}$.
  have hfg_const : ∃ M, ∀ n, f (g n) ≤ M := by
    exact ⟨ Finset.sup ( Finset.range ( C + 1 ) ) ( fun n ↦ f n ), fun n ↦ Finset.le_sup ( f := fun n ↦ f n ) ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ( hC n ) ) ) ⟩;
  obtain ⟨ M, hM ⟩ := hfg_const;
  -- Since $f(g(n)) \leq M$ for all $n$, we can apply the definition of `bigO` with the constant function $M$.
  have hfg_const : (fun n ↦ f (g n) : ℕ → ℤ) =O[.atTop] (fun _ ↦ M : ℕ → ℤ) := by
    exact Asymptotics.isBigO_iff.mpr ⟨ 1, by aesop ⟩;
  convert hfg_const.trans _
  norm_num [ Asymptotics.isBigO_iff ];
  exact ⟨ M, 0, fun _ _ ↦ le_rfl ⟩

theorem const_comp (hf : f ∈ const) (g) : f ∘ g ∈ const := by
  obtain ⟨C, hC⟩ := bounded_of_const hf
  norm_num [const, Asymptotics.isBigO_iff, bigO];
  use C, 0
  exact fun _ _ ↦ mod_cast (hC _)

/-- Any LawfulGrowthRate is closed under linear transformation on the output. -/
theorem linear_comp (hf : f ∈ linear) (hg : g ∈ S) : f ∘ g ∈ S := by
  refine' ‹S.LawfulGrowthRate›.mem_dominating _ _;
  refine' fun n ↦ ( f ∘ g ) n;
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl;
  · -- Since $f$ is in the linear growth rate, there exists a constant $C$ such that $f(n) \leq C \cdot n$ for all $n$.
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, f n ≤ C * (n + 1) := by
      obtain ⟨ C, hC ⟩ := Asymptotics.isBigO_iff.mp hf;
      norm_num at *;
      obtain ⟨ a, ha ⟩ := hC;
      use ⌈C⌉₊ + ∑ n ∈ Finset.range a, f n;
      intro n; by_cases hn : n < a;
      · nlinarith [ Finset.single_le_sum ( fun x _ ↦ Nat.zero_le ( f x ) ) ( Finset.mem_range.mpr hn ) ];
      · exact_mod_cast ( by nlinarith [ Nat.le_ceil C, ha n ( le_of_not_gt hn ), show ( ∑ n ∈ Finset.range a, f n : ℝ ) ≥ 0 by exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _ ] : ( f n : ℝ ) ≤ ( ⌈C⌉₊ + ∑ n ∈ Finset.range a, f n ) * ( n + 1 ) );
    -- Since $g$ is in $S$, we have $C * (g n + 1)$ is also in $S$ because $S$ is closed under multiplication by a constant.
    have h_mul : (fun n ↦ C * (g n + 1)) ∈ S := by
      have h_mul : (fun n ↦ g n + 1) ∈ S := by
        exact ‹S.LawfulGrowthRate›.mem_add hg ( by simpa using ‹S.LawfulGrowthRate›.one_mem );
      have h_mul : ∀ k : ℕ, (fun n ↦ k * (g n + 1)) ∈ S := by
        intro k; induction k <;> simp_all [ Nat.succ_mul ] ;
        · exact ‹S.LawfulGrowthRate›.mem_dominating ( by norm_num ) ( ‹S.LawfulGrowthRate›.one_mem );
        · exact ‹S.LawfulGrowthRate›.mem_add ‹_› ‹_›;
      exact h_mul C;
    exact ‹S.LawfulGrowthRate›.mem_dominating ( Filter.Eventually.of_forall fun n ↦ by simpa using hC ( g n ) ) h_mul

section instances

def instLawfulBigO
      (hf : ∃ a, ∀ (b : ℕ), a ≤ b → 0 < f b)
      (hf₂ : ∀ k ∈ bigO f, ∀ g ≤ id, k ∘ g ∈ bigO f) :
    LawfulGrowthRate (bigO f) where
  mem_dominating h hf := by
    simp only [bigO, Asymptotics.isBigO_iff, Int.norm_natCast, Filter.eventually_atTop] at h hf ⊢
    obtain ⟨a₁, hf₁⟩ := h
    obtain ⟨c, a₂, hg⟩ := hf
    refine ⟨c, max a₁ a₂, fun b hb ↦ ?_⟩
    grw [hf₁, hg]
    · exact le_of_max_le_right hb
    · exact le_of_max_le_left hb
  mem_add hf hg := hf.add hg
  one_mem := by
    simp_rw [bigO, Asymptotics.isBigO_iff]
    use 1
    simpa using hf
  comp_le_id hf hg := hf₂ _ hf _ hg

def instLawfulLittleO (hf : 1 ∈ littleO f) (hf₂ : ∀ k g, k ∈ littleO f → (∀ x, g x ≤ x) → (k ∘ g) ∈ littleO f) :
    LawfulGrowthRate (littleO f) where
  mem_dominating h hf := by
    simp only [Filter.eventually_atTop, littleO, Asymptotics.isLittleO_iff, Int.norm_natCast] at h hf ⊢
    intro c₀ hc₀
    obtain ⟨a₁, hf₁⟩ := h
    obtain ⟨a₂, hg⟩ := hf hc₀
    refine ⟨max a₁ a₂, fun b hb ↦ ?_⟩
    grw [hf₁, hg]
    · exact le_of_max_le_right hb
    · exact le_of_max_le_left hb
  mem_add hf hg := hf.add hg
  one_mem := hf
  comp_le_id := hf₂ _ _

instance : LawfulGrowthRate const := by
  apply instLawfulBigO
  · simp
  · exact fun k a g a_1 ↦ const_comp a g

instance : LawfulGrowthRate log := by
  apply instLawfulBigO
  · use 2
    exact fun _ ↦ Nat.log_pos one_lt_two
  · intro k hk g hg;
    have h_log_le : ∀ n, Nat.log 2 (g n) ≤ Nat.log 2 n := by
      exact fun n => Nat.log_mono_right <| hg n;
    rw [ GrowthRate.bigO ] at *;
    obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, k n ≤ C * Nat.log 2 n := by
      simp +zetaDelta at *;
      rw [ Asymptotics.isBigO_iff' ] at hk;
      norm_num +zetaDelta at *;
      obtain ⟨ c, hc, N, hN ⟩ := hk; exact ⟨ ⌈c⌉₊, N, fun n hn => by exact_mod_cast le_trans ( hN n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩ ;
    refine' Asymptotics.isBigO_iff.mpr _;
    use C + ∑ n ∈ Finset.range (N + 1), k n + 1;
    norm_num;
    use N + 1;
    intro b hb;
    by_cases hgb : g b ≥ N;
    · exact le_trans ( Nat.cast_le.mpr ( hC _ hgb ) ) ( by norm_cast; nlinarith [ h_log_le b, show ∑ x ∈ Finset.range ( N + 1 ), ( k x : ℕ ) ≥ 0 by exact Nat.zero_le _ ] );
    · norm_cast;
      exact le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( k x ) ) ( Finset.mem_range.mpr ( by linarith : g b < N + 1 ) ) ) ( by nlinarith [ Nat.zero_le ( ∑ x ∈ Finset.range ( N + 1 ), k x ), Nat.log_pos one_lt_two ( by linarith : 1 < b ) ] )

--TODO move
open GrowthRate Filter Asymptotics in
lemma polylog_mem_dominating {f g : ℕ → ℕ} (h : ∀ᶠ x in atTop, g x ≤ f x) (hf : f ∈ polylog) : g ∈ polylog := by
  obtain ⟨ C, hf ⟩ := hf;
  -- Since $g$ is eventually less than or equal to $f$, and $f$ is in $polylog$, we can use the transitivity of big-O to show that $g$ is also in $polylog$.
  have h_trans : (fun n => (g n : ℤ)) =O[Filter.atTop] (fun n => (Nat.log 2 n ^ C : ℤ)) := by
    rw [ Asymptotics.isBigO_iff ] at *;
    norm_num +zetaDelta at *;
    exact ⟨ hf.choose, Max.max h.choose hf.choose_spec.choose, fun n hn => le_trans ( Nat.cast_le.mpr ( h.choose_spec n ( le_trans ( le_max_left _ _ ) hn ) ) ) ( hf.choose_spec.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ) ⟩;
  exact ⟨ C, by simpa using h_trans ⟩

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
  one_mem := by
    use 0
    simp only [Nat.cast_one, pow_zero, Asymptotics.isBigO_one_iff]
    use 1
    simp
  comp_le_id {f g} hf hg := by
    rcases hf with ⟨ C, hC ⟩;
    -- Let $M$ be such that $f(n) \leq K (\log n)^C$ for $n \geq M$.
    obtain ⟨K, hK⟩ : ∃ K, ∀ n ≥ K, f n ≤ K * (Nat.log 2 n ^ C) := by
      norm_num [ Asymptotics.isBigO_iff, Filter.eventually_atTop ] at *;
      obtain ⟨ c, a, hc ⟩ := hC; exact ⟨ ⌈c⌉₊ + a, fun n hn => by exact_mod_cast ( by nlinarith [ Nat.le_ceil c, hc n ( by linarith ), pow_nonneg ( Nat.cast_nonneg ( Nat.log 2 n ) : ( 0 :ℝ ) ≤ Nat.log 2 n ) C ] : ( f n :ℝ ) ≤ ( ⌈c⌉₊ + a ) * Nat.log 2 n ^ C ) ⟩ ;
    -- Let $B$ be such that $f(n) \leq B$ for $n < M$.
    obtain ⟨B, hB⟩ : ∃ B, ∀ n < K, f n ≤ B := by
      exact ⟨ Finset.sup ( Finset.range K ) f, fun n hn => Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
    use C + 1;
    refine' Asymptotics.IsBigO.of_bound ( K + B + 1 ) _;
    filter_upwards [ Filter.eventually_ge_atTop K, Filter.eventually_gt_atTop 1 ] with n hn hn';
    norm_num [ pow_succ' ];
    by_cases h : g n < K;
    · exact le_trans ( Nat.cast_le.mpr ( hB _ h ) ) ( by norm_cast; nlinarith [ show 0 < Nat.log 2 n * Nat.log 2 n ^ C by exact mul_pos ( Nat.log_pos one_lt_two hn' ) ( pow_pos ( Nat.log_pos one_lt_two hn' ) _ ) ] );
    · refine' le_trans ( Nat.cast_le.mpr ( hK _ ( by linarith ) ) ) _;
      norm_cast;
      gcongr;
      · linarith;
      · exact le_trans ( pow_le_pow_left' ( Nat.log_mono_right <| hg n ) _ ) ( le_mul_of_one_le_left ( by positivity ) <| Nat.le_log_of_pow_le ( by norm_num ) <| by linarith )

instance : LawfulGrowthRate sqrt :=  by
  apply instLawfulBigO
  · use 1
    intros
    positivity
  · simp [ GrowthRate.bigO, Asymptotics.IsBigO ];
    intro k x hk g hg;
    have := hk;
    norm_num [ Asymptotics.IsBigOWith ] at *;
    obtain ⟨ a, ha ⟩ := this;
    -- Let's choose $c = \max_{0 \leq i \leq a} k(i)$.
    obtain ⟨c, hc⟩ : ∃ c, ∀ i ≤ a, k i ≤ c := by
      exact ⟨ Finset.sup ( Finset.range ( a + 1 ) ) k, fun i hi => Finset.le_sup ( f := k ) ( Finset.mem_range_succ_iff.mpr hi ) ⟩;
    use Max.max c ( ⌈x⌉₊ ), a + 1;
    intro b hb;
    by_cases h : g b ≤ a;
    · exact le_trans ( Nat.cast_le.mpr ( hc _ h ) ) ( le_trans ( mod_cast le_max_left _ _ ) ( le_mul_of_one_le_right ( by positivity ) ( mod_cast Nat.sqrt_pos.mpr ( by linarith ) ) ) );
    · refine le_trans (ha _ ?_) ?_
      · linarith;
      · gcongr;
        · exact le_max_of_le_right ( Nat.le_ceil _ );
        · exact hg b

instance : LawfulGrowthRate sublinear := instLawfulLittleO
  (by simpa [GrowthRate.littleO] using tendsto_natCast_atTop_atTop)
  (by
    intro k g hk hg
    unfold GrowthRate.littleO at *;
    norm_num [ Asymptotics.isLittleO_iff ] at *;
    intro c hc_pos
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, k n ≤ (c / 2) * n := by
      exact hk ( half_pos hc_pos );
    use N + ⌈(2 * (∑ i ∈ Finset.range N, k i)) / c⌉₊ + 1;
    intro n hn
    by_cases hgn : g n < N;
    · have := Nat.le_ceil ( 2 * ( ∑ i ∈ Finset.range N, k i ) / c );
      rw [ div_le_iff₀ ] at this <;> nlinarith [ show ( k ( g n ) : ℝ ) ≤ ∑ i ∈ Finset.range N, k i from mod_cast Finset.single_le_sum ( fun i _ => Nat.zero_le ( k i ) ) ( Finset.mem_range.mpr hgn ), show ( n : ℝ ) ≥ N + ⌈2 * ( ∑ i ∈ Finset.range N, k i ) / c⌉₊ + 1 by exact_mod_cast hn ];
    · exact le_trans ( hN _ ( le_of_not_gt hgn ) ) ( by nlinarith [ show ( g n : ℝ ) ≤ n by exact_mod_cast hg n ] )
    )

instance : LawfulGrowthRate linear := by
  apply instLawfulBigO
  · use 1
    exact fun _ ↦ id
  · intro k hk g hg;
    unfold GrowthRate.bigO at *;
    -- Since $k$ is $O(id)$, there exists $C$ and $N$ such that for all $x \geq N$, $k(x) \leq C * x$.
    obtain ⟨C, N, hC⟩ : ∃ C N, ∀ x ≥ N, k x ≤ C * x := by
      norm_num [ Asymptotics.isBigO_iff ] at hk;
      obtain ⟨ c, N, hc ⟩ := hk; exact ⟨ ⌈c⌉₊, N, fun n hn => by exact_mod_cast le_trans ( hc n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩ ;
    refine' Asymptotics.IsBigO.of_bound ( C + ∑ x ∈ Finset.range N, k x + 1 ) ( Filter.eventually_atTop.mpr ⟨ N, fun x hx => _ ⟩ );
    by_cases hx' : g x < N <;> simp_all [ add_mul ];
    · exact le_add_of_le_of_nonneg ( le_add_of_nonneg_of_le ( by positivity ) ( mod_cast by nlinarith [ show k ( g x ) ≤ ∑ x ∈ Finset.range N, k x from Finset.single_le_sum ( fun a _ => Nat.zero_le ( k a ) ) ( Finset.mem_range.mpr hx' ) ] ) ) ( by positivity );
    · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( mod_cast hC _ hx' |> le_trans <| Nat.mul_le_mul_left _ <| hg x ) <| by positivity ) <| by positivity;

instance : LawfulGrowthRate linearithmic := by
  apply instLawfulBigO
  · use 2
    intro n hn
    nlinarith [Nat.log_pos one_lt_two hn]
  · intro k hk g hg
    obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, k n ≤ C * n * Nat.log 2 n := by
      rcases hk.exists_pos with ⟨ C, hC_pos, hC ⟩;
      rw [ Asymptotics.isBigOWith_iff ] at hC;
      norm_num +zetaDelta at *;
      exact ⟨ ⌈C⌉₊, hC.choose, fun n hn => by rw [ ← @Nat.cast_le ℝ ] ; push_cast; nlinarith [ Nat.le_ceil C, hC.choose_spec n hn, show ( n : ℝ ) * Nat.log 2 n ≥ 0 by positivity ] ⟩;
    refine' Asymptotics.IsBigO.of_bound _ _;
    exact ( ∑ n ∈ Finset.range N, k n ) + C;
    simp +zetaDelta at *;
    refine' ⟨ N + 2, fun n hn => _ ⟩;
    by_cases hgn : g n < N;
    · exact le_trans ( mod_cast Finset.single_le_sum ( fun x _ => Nat.zero_le ( k x ) ) ( Finset.mem_range.mpr hgn ) ) ( le_trans ( le_add_of_nonneg_right <| Nat.cast_nonneg _ ) <| le_mul_of_one_le_right ( by positivity ) <| one_le_mul_of_one_le_of_one_le ( mod_cast by linarith ) <| mod_cast Nat.le_log_of_pow_le ( by linarith ) <| by linarith );
    · refine' le_trans ( Nat.cast_le.mpr ( hC _ ( by linarith ) ) ) _;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_add_of_nonneg_left <| Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) <| by positivity );
      simpa [ mul_assoc ] using mul_le_mul_of_nonneg_left ( mul_le_mul ( Nat.cast_le.mpr ( hg n ) ) ( Nat.cast_le.mpr ( Nat.log_mono_right ( hg n ) ) ) ( by positivity ) ( by positivity ) ) ( by positivity )

--TODO: Move, cleanup

noncomputable section AristotleLemmas

lemma quasilinear_bound_mono (C : ℕ) : Monotone (fun n ↦ n * (Nat.log 2 n) ^ C) := by
  exact fun a b hab => Nat.mul_le_mul hab ( Nat.pow_le_pow_left ( Nat.log_mono_right hab ) _ )

lemma isBigO_quasilinear_bound_comp_le_id (C : ℕ) (g : ℕ → ℕ) (hg : g ≤ id) :
    (fun n ↦ ((g n) * (Nat.log 2 (g n)) ^ C : ℤ)) =O[.atTop] (fun n ↦ (n * (Nat.log 2 n) ^ C : ℤ)) := by
  refine' Asymptotics.IsBigO.of_bound 1 _;
  simp +zetaDelta at *;
  exact ⟨ 1, fun n hn => mul_le_mul ( mod_cast hg n ) ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( mod_cast Nat.log_mono_right <| hg n ) _ ) ( by positivity ) ( by positivity ) ⟩

lemma isBigO_comp_bound_plus_const {f h : ℕ → ℕ} (hf : (f · : ℕ → ℤ) =O[.atTop] (h · : ℕ → ℤ)) (g : ℕ → ℕ) :
    (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ (h (g n) : ℤ) + 1) := by
  -- First, we simplify the hypothesis hf to obtain the constants C and N.
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, (f n : ℤ) ≤ C * (h n : ℤ) := by
    rw [ Asymptotics.isBigO_iff' ] at hf;
    norm_num +zetaDelta at *;
    exact ⟨ ⌈hf.choose⌉₊, hf.choose_spec.2.choose, fun n hn => by exact_mod_cast le_trans ( hf.choose_spec.2.choose_spec n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩;
  -- Let's choose M to be the maximum value of |f(x)| for x < N.
  obtain ⟨M, hM⟩ : ∃ M, ∀ x < N, (f x : ℤ) ≤ M := by
    exact ⟨ ∑ x ∈ Finset.range N, ( f x : ℤ ), fun x hx => Finset.single_le_sum ( fun x _ => Nat.cast_nonneg ( f x ) ) ( Finset.mem_range.mpr hx ) ⟩;
  refine' Asymptotics.IsBigO.of_bound ( Max.max M ( |C| ) ) _;
  filter_upwards [ Filter.eventually_gt_atTop N ] with x hx;
  by_cases hgx : g x < N;
  · norm_num [ Norm.norm ];
    exact le_trans ( mod_cast hM _ hgx ) ( le_trans ( le_max_left _ _ ) ( le_mul_of_one_le_right ( by positivity ) ( mod_cast by linarith [ Nat.zero_le ( h ( g x ) ) ] ) ) );
  · norm_num [ Norm.norm ];
    norm_cast;
    simp +zetaDelta at *;
    cases abs_cases C <;> nlinarith [ hC ( g x ) hgx, le_max_left M |C|, le_max_right M |C| ]

lemma one_isBigO_quasilinear_bound (C : ℕ) :
    (fun _ ↦ (1 : ℤ)) =O[.atTop] (fun n ↦ (n * (Nat.log 2 n) ^ C : ℤ)) := by
  rw [ Asymptotics.isBigO_iff ];
  use 1; norm_num;
  exact ⟨ 2, fun n hn => one_le_mul_of_one_le_of_one_le ( by norm_cast; linarith ) ( one_le_pow₀ ( mod_cast Nat.log_pos one_lt_two ( by linarith ) ) ) ⟩

end AristotleLemmas

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
  one_mem := by
    use 0
    simp [Asymptotics.isBigO_iff]
    use 1, 1
    intro b hb
    simp [hb]
  comp_le_id := by
    intro f g hf hg
    obtain ⟨C, hC⟩ := hf
    use C;
    have h_comp : (fun n => (f (g n) : ℤ)) =O[.atTop] (fun n => (g n * (Nat.log 2 (g n)) ^ C : ℤ) + 1) := by
      convert GrowthRate.isBigO_comp_bound_plus_const hC g using 1;
      norm_cast;
    have h_comp_bound : (fun n => ((g n) * (Nat.log 2 (g n)) ^ C : ℤ)) =O[.atTop] (fun n => (n * (Nat.log 2 n) ^ C : ℤ)) := by
      exact isBigO_quasilinear_bound_comp_le_id C g hg;
    have h_comp_bound_plus_one : (fun n => ((g n) * (Nat.log 2 (g n)) ^ C : ℤ) + 1) =O[.atTop] (fun n => (n * (Nat.log 2 n) ^ C : ℤ)) := by
      refine' h_comp_bound.add ( _ );
      exact one_isBigO_quasilinear_bound C;
    simpa using h_comp.trans h_comp_bound_plus_one

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
  one_mem := by
    use 0
    simp [Asymptotics.isBigO_iff]
    use 1, 0
    simp
  comp_le_id := by
    intro f g hf hg
    obtain ⟨C, hC⟩ := hf;
    have h_bound : ∃ K, ∀ᶠ n in Filter.atTop, f (g n) ≤ K * n ^ C := by
      obtain ⟨K, N, hK⟩ : ∃ K N, ∀ n ≥ N, f n ≤ K * n ^ C := by
        rw [ Asymptotics.isBigO_iff' ] at hC;
        rcases hC with ⟨ K, hK₀, hK ⟩ ; rcases Filter.eventually_atTop.mp hK with ⟨ N, hN ⟩ ; exact ⟨ ⌈K⌉₊, N, fun n hn => by simpa [ ← @Nat.cast_le ℝ ] using le_trans ( hN n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩ ;
      use K + ∑ n ∈ Finset.range N, f n;
      filter_upwards [ Filter.eventually_ge_atTop N ] with n hn;
      by_cases hgn : g n < N;
      · exact le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( f x ) ) ( Finset.mem_range.mpr hgn ) ) ( Nat.le_trans ( Nat.le_add_left _ _ ) ( Nat.le_mul_of_pos_right _ ( pow_pos ( by linarith ) _ ) ) );
      · exact le_trans ( hK _ ( by linarith ) ) ( Nat.mul_le_mul_right _ ( Nat.le_add_right _ _ ) |> le_trans ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left ( hg n ) _ ) ) );
    obtain ⟨ K, hK ⟩ := h_bound;
    use C
    rw [ Asymptotics.isBigO_iff ];
    exact ⟨ K, by filter_upwards [ hK ] with n hn; simpa using mod_cast hn ⟩

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
  one_mem := ⟨0, by simp⟩
  comp_le_id := by
    intro f g hf hg;
    -- Since $g \leq \text{id}$, we have $(Nat.log 2 (g n)) \leq (Nat.log 2 n)$. Therefore, $(Nat.log 2 (g n))^C \leq (Nat.log 2 n)^C$.
    have h_log_le : ∀ n, (Nat.log 2 (g n))^hf.choose ≤ (Nat.log 2 n)^hf.choose := by
      exact fun n => Nat.pow_le_pow_left ( Nat.log_mono_right <| hg n ) _;
    have h_exp_le : ∀ n, 2 ^ ((Nat.log 2 (g n)) ^ hf.choose) ≤ 2 ^ ((Nat.log 2 n) ^ hf.choose) := by
      exact fun n => pow_le_pow_right₀ ( by decide ) ( h_log_le n );
    use hf.choose;
    -- Since $f \in \text{quasipoly}$, there exists a constant $C$ such that $f(n) \leq C \cdot 2^{(\log n)^C}$.
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, f n ≤ C * 2 ^ ((Nat.log 2 n) ^ hf.choose) := by
      have := hf.choose_spec;
      -- By definition of bigO, there exists a constant C and an N such that for all n ≥ N, f(n) ≤ C * 2^(Nat.log 2 n)^hf.choose.
      obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * 2 ^ (Nat.log 2 n) ^ hf.choose := by
        rw [ Asymptotics.isBigO_iff ] at this;
        norm_num at *;
        obtain ⟨ c, N, hN ⟩ := this;
        norm_num [ Norm.norm ] at hN;
        exact ⟨ ⌈c⌉₊, N, fun n hn => by exact_mod_cast le_trans ( hN n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩;
      use C + ∑ n ∈ Finset.range N, f n + 1;
      -- For any $n$, if $n < N$, then $f n \leq \sum_{k=0}^{N-1} f k$.
      intros n
      by_cases hn : n < N;
      · nlinarith [ Finset.single_le_sum ( fun x _ => Nat.zero_le ( f x ) ) ( Finset.mem_range.mpr hn ), Nat.one_le_pow ( Nat.log 2 n ^ hf.choose ) 2 zero_lt_two ];
      · exact le_trans ( hC n ( le_of_not_gt hn ) ) ( Nat.mul_le_mul_right _ ( by linarith [ Nat.zero_le ( ∑ n ∈ Finset.range N, f n ) ] ) );
    refine' Asymptotics.IsBigO.of_bound C _;
    norm_num +zetaDelta at *;
    exact ⟨ 1, fun n hn => by erw [ Real.norm_of_nonneg ( by positivity ) ] ; exact_mod_cast le_trans ( hC _ ) ( mul_le_mul_of_nonneg_left ( mod_cast h_exp_le _ ) ( Nat.cast_nonneg _ ) ) ⟩

instance : LawfulGrowthRate two_pow := by
  apply instLawfulBigO
  · use 0
    intros
    positivity
  · intros k hk g hg;
    -- By definition of bigO, there exists a constant C such that k(n) ≤ C * 2^n for all n.
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, k n ≤ C * 2 ^ n := by
      have := hk;
      -- By definition of bigO, there exists a constant C such that for all sufficiently large n, k(n) ≤ C * 2^n.
      obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, k n ≤ C * 2 ^ n := by
        obtain ⟨ C, hC ⟩ := this.exists_pos;
        rw [ Asymptotics.isBigOWith_iff ] at hC;
        norm_num [ Norm.norm ] at hC;
        exact ⟨ ⌈C⌉₊, Filter.eventually_atTop.mpr ⟨ hC.2.choose, fun n hn => by exact_mod_cast hC.2.choose_spec n hn |> le_trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| by positivity ⟩ ⟩;
      simp +zetaDelta at *;
      -- Let $M$ be the maximum value of $k(n)$ for $n < a$.
      obtain ⟨M, hM⟩ : ∃ M, ∀ n < hC.choose, k n ≤ M := by
        exact ⟨ Finset.sup ( Finset.range hC.choose ) k, fun n hn => Finset.le_sup ( f := k ) ( Finset.mem_range.mpr hn ) ⟩;
      exact ⟨ Max.max C M, fun n => if hn : n < hC.choose then le_trans ( hM n hn ) ( by nlinarith [ Nat.le_max_left C M, Nat.le_max_right C M, Nat.one_le_pow n 2 zero_lt_two ] ) else le_trans ( hC.choose_spec n ( le_of_not_gt hn ) ) ( by nlinarith [ Nat.le_max_left C M, Nat.le_max_right C M, Nat.one_le_pow n 2 zero_lt_two ] ) ⟩;
    -- Since $g(x) \leq x$, we have $k(g(x)) \leq C * 2^{g(x)} \leq C * 2^x$.
    have h_comp : ∀ x, k (g x) ≤ C * 2 ^ x := by
      exact fun x => le_trans ( hC _ ) ( Nat.mul_le_mul_left _ ( pow_le_pow_right₀ ( by decide ) ( hg x ) ) );
    refine' Asymptotics.IsBigO.of_bound ( C + 1 ) _;
    -- Since $C * 2^x$ is already less than or equal to $(C + 1) * 2^x$, the inequality holds for all $x$.
    simp
    exact ⟨ 0, fun n hn => by erw [ Real.norm_of_nonneg ( by norm_num ) ] ; exact_mod_cast le_trans ( h_comp n ) ( by gcongr ; linarith ) ⟩

instance : LawfulGrowthRate e_pow := by
  apply instLawfulBigO
  · use 0
    intros
    positivity
  · intro k hk g hg
    obtain ⟨C, hC⟩ : ∃ C, ∀ n, k n ≤ C * ⌈Real.exp n⌉₊ := by
      obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, k n ≤ C * ⌈Real.exp n⌉₊ := by
        have h_def : ∃ C N, ∀ n ≥ N, k n ≤ C * ⌈Real.exp n⌉₊ := by
          have h_def : (k · : ℕ → ℤ) =O[.atTop] (fun n : ℕ => ⌈Real.exp n⌉₊ : ℕ → ℤ) := by
            exact hk
          rw [ Asymptotics.isBigO_iff ] at h_def;
          norm_num +zetaDelta at *;
          obtain ⟨ c, a, h ⟩ := h_def; exact ⟨ ⌈c⌉₊, a, fun n hn => by exact_mod_cast le_trans ( h n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩ ;
        exact h_def;
      obtain ⟨M, hM⟩ : ∃ M, ∀ n < N, k n ≤ M := by
        exact ⟨ Finset.sup ( Finset.range N ) k, fun n hn => Finset.le_sup ( f := k ) ( Finset.mem_range.mpr hn ) ⟩;
      exact ⟨ Max.max C M, fun n => if hn : n < N then le_trans ( hM n hn ) ( by nlinarith [ Nat.ceil_pos.mpr ( Real.exp_pos n ), le_max_right C M ] ) else le_trans ( hC n ( le_of_not_gt hn ) ) ( by nlinarith [ Nat.ceil_pos.mpr ( Real.exp_pos n ), le_max_left C M ] ) ⟩;
    have h_comp : ∀ n, k (g n) ≤ C * ⌈Real.exp (g n)⌉₊ := by
      exact fun n => hC _;
    refine' Asymptotics.IsBigO.of_bound C _;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by simpa using mod_cast h_comp n |> le_trans <| mul_le_mul_of_nonneg_left ( Nat.ceil_mono <| Real.exp_le_exp.mpr <| Nat.cast_le.mpr <| hg n ) <| Nat.cast_nonneg _;

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
  one_mem := by use 1; simp; use 1; simp
  comp_le_id {f g} hf hg := by
    obtain ⟨C, hC⟩ : ∃ C, f ∈ bigO (fun n => C ^ n) := by
      obtain ⟨ C, hC ⟩ := hf;
      exact ⟨ C, mod_cast hC ⟩;
    -- Since g(n) ≤ n, if C ≥ 1, then C^{g(n)} ≤ C^n. If C = 0, then f(n) is eventually 0, so f(g(n)) is eventually 0, which is O(1^n).
    by_cases hC_ge_1 : C ≥ 1;
    · -- Since $g(n) \leq n$, we have $C^{g(n)} \leq C^n$ for all $n$.
      have h_exp_g : (fun n => C ^ g n) ∈ bigO (fun n => C ^ n) := by
        refine' Asymptotics.isBigO_iff.mpr _;
        exact ⟨ 1, Filter.Eventually.of_forall fun n => by simpa using pow_le_pow_right₀ ( mod_cast hC_ge_1 ) ( hg n ) ⟩;
      -- Since $f \in \text{bigO}(C^n)$, we have $f(g(n)) \in \text{bigO}(C^{g(n)})$.
      have h_f_g : f ∘ g ∈ bigO (fun n => C ^ g n) := by
        rw [ GrowthRate.bigO ] at *;
        simp_all [ Asymptotics.isBigO_iff ];
        obtain ⟨ c, a, hc ⟩ := hC;
        use Max.max c ( ∑ x ∈ Finset.range ( a + 1 ), ( f x : ℝ ) / ( C ^ x : ℝ ) ), a + 1;
        intro b hb;
        by_cases hgb : g b ≤ a;
        · exact le_trans ( show ( f ( g b ) : ℝ ) ≤ ( ∑ x ∈ Finset.range ( a + 1 ), ( f x : ℝ ) / C ^ x ) * C ^ g b from by rw [ Finset.sum_mul _ _ _ ] ; exact le_trans ( by rw [ div_mul_cancel₀ _ ( by positivity ) ] ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_range.mpr ( by linarith ) ) ) ) ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) );
        · exact le_trans ( hc _ ( by linarith ) ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) );
      -- Since $C^{g(n)} \leq C^n$ for all $n$, we have $f(g(n)) \in \text{bigO}(C^n)$.
      have h_f_g_final : f ∘ g ∈ bigO (fun n => C ^ n) := by
        apply_rules [ Asymptotics.IsBigO.trans ];
      -- Since $C \geq 1$, we have $C^n \in \text{bigO}(C^n)$.
      use C;
      convert h_f_g_final using 1;
      unfold GrowthRate.bigO; aesop;
    · -- Since C is not greater than or equal to 1, we have C = 0.
      have hC_zero : C = 0 := by
        exact Nat.eq_zero_of_not_pos hC_ge_1;
      have h_eventually_zero : ∃ N, ∀ n ≥ N, f n = 0 := by
        have := hC;
        norm_num [ hC_zero, GrowthRate.bigO ] at this;
        rw [ Asymptotics.isBigO_iff ] at this;
        norm_num +zetaDelta at *;
        exact ⟨ this.choose_spec.choose + 1, fun n hn => by simpa [ show n ≠ 0 by linarith ] using this.choose_spec.choose_spec n ( by linarith ) ⟩;
      obtain ⟨ N, hN ⟩ := h_eventually_zero;
      use 1;
      simp +zetaDelta at *;
      refine' ⟨ ∑ n ∈ Finset.range N, ( f n : ℝ ), Filter.eventually_atTop.mpr ⟨ N, fun n hn => _ ⟩ ⟩;
      by_cases h : g n < N <;> simp_all
      · exact_mod_cast Finset.single_le_sum ( fun a _ => Nat.cast_nonneg ( f a ) ) ( Finset.mem_range.mpr h );
      · exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

--TODO: move / cleanup

noncomputable section AristotleLemmas

/--
`runningMax f n` is the maximum value of `f k` for all `k ≤ n`. It is defined recursively: `runningMax f 0 = f 0`, and `runningMax f (n+1) = max (runningMax f n) (f (n+1))`.
-/
def runningMax (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (f 0) (fun k res ↦ max res (f (k + 1))) n

lemma runningMax_le (f : ℕ → ℕ) (n : ℕ) : f n ≤ runningMax f n := by
  induction n <;> simp [ *, GrowthRate.runningMax ]

lemma runningMax_mono (f : ℕ → ℕ) : Monotone (runningMax f) := by
  refine' monotone_nat_of_le_succ fun n => _;
  exact le_max_left _ _

/-
The step function for `runningMax` is primitive recursive.
-/
def runningMaxStep (f : ℕ → ℕ) (n res : ℕ) : ℕ := max res (f (n + 1))

lemma runningMaxStep_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (Nat.unpaired (runningMaxStep f)) := by
  have h_max : Nat.Primrec (Nat.unpaired (Nat.max)) := by
    have h_max : Nat.Primrec (Nat.unpaired (fun x y => y + (x - y))) := by
      have h_max : Nat.Primrec (Nat.unpaired (fun x y => x - y)) := by
        exact Nat.Primrec.sub;
      have h_max : Nat.Primrec (Nat.unpaired (fun x y => y + x)) := by
        have h_max : Nat.Primrec (Nat.unpaired (fun x y => x + y)) := by
          exact Nat.Primrec.add;
        simpa only [ add_comm ] using h_max;
      convert h_max.comp ( Nat.Primrec.pair ( Nat.Primrec.right ) ( ‹Nat.Primrec ( Nat.unpaired fun x y => x - y ) › ) ) using 1;
      ext ⟨x, y⟩; simp [Nat.unpaired];
      simp [ Nat.unpaired, Nat.unpair_pair ];
      ring;
    grind;
  convert h_max.comp ( Nat.Primrec.pair _ _ ) using 1;
  rotate_left;
  exact fun n => n.unpair.2;
  exact fun n => f ( n.unpair.1 + 1 );
  · exact Nat.Primrec.right;
  · have h_comp : Nat.Primrec (fun n => f (n + 1)) := by
      have h_succ : Nat.Primrec (fun n => n + 1) := by
        exact Nat.Primrec.succ
      exact hf.comp h_succ;
    have h_unpair : Nat.Primrec (fun n => Nat.unpair n |>.1) := by
      exact Nat.Primrec.left;
    exact h_comp.comp h_unpair;
  · unfold GrowthRate.runningMaxStep; aesop;

/-
If `f` is primitive recursive, then `runningMax f` is primitive recursive.
-/
lemma runningMax_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (runningMax f) := by
  -- Define the initial value `c` as `f 0`.
  set c := f 0;
  -- Define the step function for `runningMax` as `Nat.unpaired (runningMaxStep f)`.
  set step := Nat.unpaired (runningMaxStep f);
  have h_step_prim : Nat.Primrec step := by
    exact runningMaxStep_primrec hf;
  -- We can use the fact that `runningMax` is defined recursively to show it is primitive recursive.
  have h_rec : ∀ n, runningMax f n = Nat.rec c (fun n res => step (Nat.pair n res)) n := by
    intro n; induction n <;> aesop;
  rw [ show GrowthRate.runningMax f = _ from funext h_rec ];
  exact Nat.Primrec.prec1 c h_step_prim

/--
Every primitive recursive function is dominated (in the Big-O sense) by a monotone primitive recursive function.
-/
lemma Primrec.exists_monotone_dominating {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ g, Nat.Primrec g ∧ Monotone g ∧ f ∈ GrowthRate.bigO g := by
      use runningMax f
      and_intros
      · exact runningMax_primrec hf
      · exact runningMax_mono f
      · exact Asymptotics.isBigO_of_le _ (by simpa using runningMax_le f)

/--
If a monotone function `h : ℕ → ℕ` is not the zero function, then it is eventually at least 1.
-/
lemma monotone_nat_eventually_pos {h : ℕ → ℕ} (h_mono : Monotone h) (h_not_zero : h ≠ 0) :
    ∀ᶠ n in Filter.atTop, 1 ≤ h n := by
  exact Filter.eventually_atTop.mpr <| by
    obtain ⟨ n, hn ⟩ := Function.ne_iff.mp h_not_zero
    exact ⟨ n, fun m hm => Nat.pos_of_ne_zero fun hnm => hn <| by have := h_mono hm; aesop⟩

lemma bigO_comp_le_id_of_pos {f g h : ℕ → ℕ} (h_mono : Monotone h) (h_pos : ∀ n, 1 ≤ h n) (hg : g ≤ id) (hf : f ∈ GrowthRate.bigO h) : f ∘ g ∈ GrowthRate.bigO h := by
  -- Since `f ∈ bigO h`, there exist constants `C` and `N` such that `∀ n ≥ N, f n ≤ C * h n`.
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * h n := by
    have := hf;
    rcases Asymptotics.isBigO_iff.mp this with ⟨ C, hC ⟩;
    norm_num [ Norm.norm ] at hC;
    exact ⟨ ⌈C⌉₊, hC.choose, fun n hn => by have := hC.choose_spec n hn; exact_mod_cast this.trans ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩;
  -- Let's define M as the maximum of f(k) for k < N.
  set M := Finset.sup (Finset.range N) (fun k => f k);
  refine' Asymptotics.IsBigO.of_bound ( C + M ) ( Filter.eventually_atTop.2 ⟨ N, fun n hn => _ ⟩ );
  by_cases hgn : g n ≥ N;
  · norm_num;
    exact_mod_cast le_trans ( hC _ hgn ) ( Nat.mul_le_mul_right _ ( Nat.le_add_right _ _ ) ) |> le_trans <| Nat.mul_le_mul_left _ <| h_mono <| hg _;
  · norm_num +zetaDelta at *;
    exact le_trans ( Nat.cast_le.mpr <| Finset.le_sup ( f := fun k => f k ) <| Finset.mem_range.mpr hgn ) <| by norm_cast; nlinarith [ h_pos n ] ;

end AristotleLemmas

instance : LawfulGrowthRate primitiveRecursive where
  mem_dominating h hf := by
    rw [primitiveRecursive, Set.mem_setOf] at hf ⊢
    peel hf with g hg hf
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    refine Asymptotics.IsBigO.trans ?_ hf;
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by simpa using mod_cast hN n hn⟩⟩
  mem_add hf hg := by
    obtain ⟨a, ha₁, ha₂⟩ := hf
    obtain ⟨b, hb₁, hb₂⟩ := hg
    simp_rw [primitiveRecursive, ← Primrec.nat_iff] at *
    exact ⟨_, Primrec.nat_add.comp ha₁ hb₁, bigO_add ha₂ hb₂⟩
  one_mem := by
    use fun _ ↦ 1
    simp [Nat.Primrec.const, GrowthRate.bigO]
    use 1
    norm_num
  comp_le_id := by
    intros f g hf hg;
    obtain ⟨ h, hh₁, hh₂ ⟩ := hf;
    -- By `Primrec.exists_monotone_dominating`, there exists `H` such that `Nat.Primrec H`, `Monotone H`, and `h = O(H)`.
    obtain ⟨ H, hH₁, hH₂, hH₃ ⟩ := Primrec.exists_monotone_dominating hh₁;
    -- Let `H' n = H n + 1`. `H'` is primitive recursive (sum of primrec and const).
    set H' : ℕ → ℕ := fun n => H n + 1
    have hH'_primrec : Nat.Primrec H' := by
      exact Nat.Primrec.succ.comp hH₁;
    -- Since `H'` is monotone and positive, and `f = O(H')`, we can apply `GrowthRate.bigO_comp_le_id_of_pos`.
    have h_comp : f ∘ g ∈ GrowthRate.bigO H' := by
      apply GrowthRate.bigO_comp_le_id_of_pos;
      · exact fun n m hnm => Nat.succ_le_succ ( hH₂ hnm );
      · exact fun n => Nat.succ_pos _;
      · assumption;
      · apply Asymptotics.IsBigO.trans hh₂
        apply Asymptotics.IsBigO.trans hH₃
        apply Asymptotics.isBigO_iff.mpr
        norm_num +zetaDelta at *;
        use 1, 0
        intro n hn
        erw [ Real.norm_of_nonneg ] <;> norm_cast <;> linarith
    exact ⟨ H', hH'_primrec, h_comp ⟩


noncomputable section AristotleLemmas

/-
For every computable function $f$, there exists a computable monotone function $g$ such that $f \le g$.
-/
lemma exists_monotone_computable_bound' {f : ℕ → ℕ} (hf : Computable f) :
    ∃ g, Computable g ∧ Monotone g ∧ ∀ n, f n ≤ g n := by
  let g := fun n ↦ ((List.range (n+1)).map f).foldl max 0
  have hg : Computable g := by
    have h_max : ∀ n, g n = Nat.recOn n ( f 0 ) ( fun n g => max g ( f ( n + 1 ) ) ) := by
      intro n;
      induction n <;> simp [*]
      · aesop;
      · simp +zetaDelta at *;
        rw [ List.range_succ ] ; aesop;
    rw [ show g = _ from funext h_max ];
    -- The recursive function is computable because it is defined using the computable function $f$.
    have h_rec : Computable (fun p : ℕ × ℕ => (p.1 + 1, max p.2 (f (p.1 + 1)))) := by
      apply Computable.pair;
      · exact Computable.succ.comp Computable.fst;
      · apply Computable.of_eq;
        rotate_right;
        exact fun p => Max.max p.2 ( f ( p.1 + 1 ) );
        · have h_max : Computable (fun (p : ℕ × ℕ) => (p.2, f (p.1 + 1))) := by
            exact Computable.pair ( Computable.snd ) ( hf.comp ( Computable.succ.comp ( Computable.fst ) ) );
          have h_max : Computable (fun (p : ℕ × ℕ) => max p.1 p.2) := by
            -- The max function is primitive recursive, hence computable.
            have h_max_primrec : Primrec (fun (p : ℕ × ℕ) => max p.1 p.2) := by
              exact Primrec.nat_max;
            exact Primrec.to_comp h_max_primrec;
          convert h_max.comp ‹Computable fun p : ℕ × ℕ => ( p.2, f ( p.1 + 1 ) ) › using 1;
        · exact fun n ↦ rfl;
    have h_iter : ∀ n, (Nat.recOn n (f 0) fun n g => max g (f (n + 1))) = (Nat.iterate (fun p : ℕ × ℕ => (p.1 + 1, max p.2 (f (p.1 + 1)))) n (0, f 0)).2 := by
      intro n; induction n <;> simp_all [ Function.iterate_succ_apply' ] ;
      rename_i n ih; erw [ show ( Nat.iterate ( fun p : ℕ × ℕ => ( p.1 + 1, Max.max p.2 ( f ( p.1 + 1 ) ) ) ) n ( 0, f 0 ) ).1 = n from Nat.recOn n rfl fun n ihn => by simp [ *, Function.iterate_succ_apply' ] ] ;
    rw [ show ( fun x => Nat.recOn x ( f 0 ) fun n g => Max.max g ( f ( n + 1 ) ) ) = fun n => ( ( fun p : ℕ × ℕ => ( p.1 + 1, Max.max p.2 ( f ( p.1 + 1 ) ) ) ) ^[ n ] ( 0, f 0 ) ).2 from funext h_iter ];
    have h_iter : Computable (fun n => (Nat.iterate (fun p : ℕ × ℕ => (p.1 + 1, max p.2 (f (p.1 + 1)))) n (0, f 0))) := by
      have h_iter : ∀ n, (Nat.iterate (fun p : ℕ × ℕ => (p.1 + 1, max p.2 (f (p.1 + 1)))) n (0, f 0)) = Nat.recOn n (0, f 0) (fun n p => (p.1 + 1, max p.2 (f (p.1 + 1)))) := by
        exact fun n => by induction n <;> simp [ *, Function.iterate_succ_apply' ] ;
      apply Computable.of_eq;
      apply Computable.nat_rec;
      exact Computable.id;
      exact Computable.const ( 0, f 0 );
      rotate_left;
      use fun n p => ( p.2.1 + 1, Max.max p.2.2 ( f ( p.2.1 + 1 ) ) );
      · exact fun n ↦
        Eq.symm (Prod.ext (congrArg Prod.fst (h_iter n)) (congrArg Prod.snd (h_iter n)));
      · convert h_rec.comp ( Computable.snd.comp ( Computable.snd ) ) using 1;
    exact Computable.snd.comp h_iter
  have hmono : Monotone g := by
    refine' monotone_nat_of_le_succ _;
    simp [ g, List.range_succ ];
    grind
  have hle : ∀ n, f n ≤ g n := by
    simp +zetaDelta at *;
    intro n; induction n <;> simp_all [ List.range_succ ] ;
  exact ⟨g, hg, hmono, hle⟩

/-
If $h$ is monotone and $\ge 1$, and $f = O(h)$ and $g \le id$, then $f \circ g = O(h)$.
-/
lemma bigO_comp_le_id {f g h : ℕ → ℕ} (hh_mono : Monotone h) (hh_pos : ∀ n, 1 ≤ h n) (hf : f ∈ bigO h) (hg : g ≤ id) : f ∘ g ∈ bigO h := by
  -- Since $f \in \text{bigO}(h)$, there exist constants $C$ and $N$ such that for all $n \geq N$, $f(n) \leq C \cdot h(n)$.
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * h n := by
    obtain ⟨ C, N, hC ⟩ := hf.exists_pos;
    rw [ Asymptotics.isBigOWith_iff ] at hC;
    rw [ Filter.eventually_atTop ] at hC; rcases hC with ⟨ N, hN ⟩ ; use ⌈C⌉₊, N; intro n hn; specialize hN n hn; norm_num [ Norm.norm ] at hN; exact_mod_cast hN.trans ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| Nat.cast_nonneg _ ) ;
  -- Let $M = \max_{k < N} f(k)$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ k < N, f k ≤ M := by
    exact ⟨ Finset.sup ( Finset.range N ) f, fun k hk => Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hk ) ⟩;
  -- For any $n$, we have $f(g(n)) \leq (C + M) \cdot h(n)$.
  have h_bound : ∀ n, f (g n) ≤ (C + M) * h n := by
    intro n; by_cases hgn : g n < N <;> simp_all [ add_mul ];
    · nlinarith [ hM ( g n ) hgn, hh_pos n ];
    · exact le_add_of_le_of_nonneg ( le_trans ( hC _ hgn ) ( Nat.mul_le_mul_left _ ( hh_mono ( hg _ ) ) ) ) ( Nat.zero_le _ );
  refine' Asymptotics.IsBigO.of_bound ( C + M ) _;
  simp +zetaDelta at *;
  exact ⟨ 0, fun n hn => mod_cast h_bound n ⟩

end AristotleLemmas

instance : LawfulGrowthRate computable where
  mem_dominating h hf := by
    rw [computable, Set.mem_setOf] at hf ⊢
    peel hf with g hg hf
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    refine Asymptotics.IsBigO.trans ?_ hf;
    rw [Asymptotics.isBigO_iff]
    use 1
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by simpa using mod_cast hN n hn⟩
  mem_add hf hg := by
    obtain ⟨a, ha₁, ha₂⟩ := hf
    obtain ⟨b, hb₁, hb₂⟩ := hg
    use a + b
    exact ⟨Primrec.nat_add.to_comp.comp ha₁ hb₁, bigO_add ha₂ hb₂⟩
  one_mem := by
    use fun _ ↦ 1
    simp [GrowthRate.bigO]
    use Computable.const 1, 1
    exact Filter.eventually_atTop.mpr ⟨0, fun _ _ ↦ by norm_num⟩
  comp_le_id {f g} hf hg := by
    obtain ⟨ g, hg₁, hg₂ ⟩ := hf;
    obtain ⟨ h', hh'₁, hh'₂ ⟩ := exists_monotone_computable_bound' hg₁;
    set h'' : ℕ → ℕ := fun n => h' n + 1
    have hh''₁ : Computable h'' :=
      Computable.succ.comp hh'₁
    have hh''₂ : Monotone h'' :=
      fun n m hnm => Nat.succ_le_succ ( hh'₂.1 hnm )
    have hh''₃ : ∀ n, 1 ≤ h'' n :=
      fun n => Nat.succ_pos _;
    have hfg : f ∈ GrowthRate.bigO h'' := by
      have hfg : f ∈ GrowthRate.bigO h' := by
        refine' Asymptotics.IsBigO.trans hg₂ _;
        exact Asymptotics.IsBigO.of_bound 1 ( Filter.eventually_atTop.mpr ⟨ 0, fun n hn => by simpa using mod_cast hh'₂.2 n ⟩ );
      refine' hfg.trans _;
      rw [ Asymptotics.isBigO_iff ];
      norm_num +zetaDelta at *;
      exact ⟨ 1, 0, fun n hn => by erw [ Real.norm_of_nonneg ] <;> norm_num ; linarith ⟩;
    exact ⟨ h'', hh''₁, GrowthRate.bigO_comp_le_id hh''₂ hh''₃ hfg hg ⟩

end instances
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
      exact ⟨ ⌈c⌉₊, a, fun n hn ↦ by exact_mod_cast ( by nlinarith [ Nat.le_ceil c, ha n hn ] : ( f n : ℝ ) ≤ ⌈c⌉₊ * Nat.log 2 n ) ⟩ ;
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
    have h_log2 : (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun x ↦ Real.log x / Real.log 2) := by
      rw [ Asymptotics.isBigO_iff' ] at *;
      simp_all [mul_div]
      exact ⟨ H.choose * |Real.log 2|, mul_pos H.choose_spec.1 ( abs_pos.mpr ( ne_of_gt ( Real.log_pos one_lt_two ) ) ), H.choose_spec.2.choose, fun n hn ↦ by rw [ le_div_iff₀ ( abs_pos.mpr ( ne_of_gt ( Real.log_pos one_lt_two ) ) ) ] ; nlinarith [ H.choose_spec.2.choose_spec n hn, abs_pos.mpr ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] ⟩;
    -- Since $\log_2(x) = \frac{\log(x)}{\log(2)}$, we can use the fact that $f = O(\log(x))$ implies $f = O(\log_2(x))$ by the properties of logarithms.
    have h_log2_nat : (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun x ↦ (Nat.log 2 x : ℝ)) := by
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
  have h_iso : ∀ f g : ℕ → ℤ, (f · : ℕ → ℤ) =O[Filter.atTop] (g · : ℕ → ℤ) ↔ (fun x ↦ f x : ℕ → ℝ) =O[Filter.atTop] (fun n ↦ g n : ℕ → ℝ) := by
    norm_num [Asymptotics.isBigO_iff, Norm.norm]
  simp [GrowthRate.polylog, h_iso]
  constructor <;> rintro ⟨C, hC⟩ <;> use C <;> refine' hC.trans _;
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

theorem linearithmic_iff_rlog {f : ℕ → ℕ} : f ∈ linearithmic ↔
    (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ x * Real.log x) := by
  -- To prove the equivalence, we can use the fact that Nat.log 2 x is asymptotically the same as log x.
  have h_log_equiv : Asymptotics.IsBigO Filter.atTop (fun x : ℕ ↦ (Nat.log 2 x : ℝ)) (fun x : ℕ ↦ Real.log x) ∧ Asymptotics.IsBigO Filter.atTop (fun x : ℕ ↦ Real.log x) (fun x : ℕ ↦ (Nat.log 2 x : ℝ)) := by
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
    have h_combined : (fun x : ℕ ↦ (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ ↦ (x * Nat.log 2 x : ℝ)) := by
      -- By definition of GrowthRate.linearithmic, if f is in linearithmic, then f is O(x * Nat.log 2 x).
      have h_def : (fun x : ℕ ↦ (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ ↦ (x * Nat.log 2 x : ℝ)) := by
        convert h using 1;
        -- By definition of GrowthRate.linearithmic, we have that f is in the big-O of x * Nat.log 2 x. Therefore, the equivalence holds.
        simp [GrowthRate.linearithmic, GrowthRate.bigO];
        norm_num [ Asymptotics.isBigO_iff ];
      exact h_def
    apply h_combined.trans
    exact Asymptotics.IsBigO.mul ( Asymptotics.isBigO_refl _ _ ) h_log_equiv.1;
  · -- Since $x \log x$ is equivalent to $x \cdot \text{Nat.log } 2 x$ in terms of growth rate, we can use the fact that $h$ implies $f$ is $O(x \cdot \text{Nat.log } 2 x)$.
    have h_equiv : (fun x : ℕ ↦ (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ ↦ (x : ℝ) * (Nat.log 2 x : ℝ)) := by
      have h_equiv : (fun x : ℕ ↦ (f x : ℝ)) =O[Filter.atTop] (fun x : ℕ ↦ (x : ℝ) * Real.log x) := by
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
    have h_log : (fun n ↦ (Nat.log 2 n : ℝ)) =O[Filter.atTop] (fun n ↦ Real.log n) := by
      rw [ Asymptotics.isBigO_iff ];
      -- We can choose $c = \frac{1}{\log 2}$.
      use 1 / Real.log 2;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ] ; simpa using Real.log_le_log ( by positivity ) ( show ( x : ℝ ) ≥ 2 ^ Nat.log 2 x by exact_mod_cast Nat.pow_log_le_self 2 ( by linarith ) ) ;
    have h_replace : (fun n ↦ (n * Nat.log 2 n ^ C : ℝ)) =O[Filter.atTop] (fun n ↦ (n * Real.log n ^ C : ℝ)) := by
      exact Asymptotics.IsBigO.mul ( Asymptotics.isBigO_refl _ _ ) ( h_log.pow _ );
    -- By transitivity of big O notation, we can combine the two results.
    have h_trans : (fun n ↦ (f n : ℝ)) =O[Filter.atTop] (fun n ↦ (n * Nat.log 2 n ^ C : ℝ)) := by
      rw [ Asymptotics.isBigO_iff ] at * ; aesop;
    exact ⟨ C, h_trans.trans h_replace ⟩;
  · simp +zetaDelta at *;
    -- Since the real logarithm and the natural logarithm are related by a constant factor, the equivalence holds.
    intros C hC
    have h_nat_log : ∃ C' : ℕ, (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun n ↦ (n : ℝ) * (Nat.log 2 n) ^ C') := by
      refine ⟨C, hC.trans ?_⟩
      have h_log : (fun n : ℕ ↦ Real.log n) =O[Filter.atTop] (fun n : ℕ ↦ (Nat.log 2 n : ℝ)) := by
        have h_log_eq : ∀ n : ℕ, n ≥ 2 → Real.log n ≤ Real.log 2 * Nat.log 2 n + Real.log 2 := by
          intro n hn
          have h_log_bound : n ≤ 2 ^ (Nat.log 2 n + 1) := by
            exact le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ );
          have := Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≤ 2 ^ ( Nat.log 2 n + 1 ) by exact_mod_cast h_log_bound ) ; norm_num [ Real.log_pow ] at * ; linarith;
        rw [ Asymptotics.isBigO_iff ];
        refine' ⟨ Real.log 2 + Real.log 2, Filter.eventually_atTop.mpr ⟨ 2, fun n hn ↦ _ ⟩ ⟩ ; rw [ Real.norm_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ), Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; nlinarith [ h_log_eq n hn, Real.log_pos one_lt_two, show ( Nat.log 2 n : ℝ ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ];
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
    simpa only [ pow_mul ] using Filter.Eventually.of_forall fun n ↦ pow_le_pow_left₀ ( abs_nonneg _ ) h_bound _;
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
  exact ⟨ Nat.max h_bound.choose h_const.choose, fun n hn ↦ le_trans ( h_bound.choose_spec n ( le_trans ( Nat.le_max_left _ _ ) hn ) ) ( pow_le_pow_right₀ ( by norm_num ) ( h_const.choose_spec n ( le_trans ( Nat.le_max_right _ _ ) hn ) ) ) ⟩

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
      obtain ⟨ c, hc, a, ha ⟩ := hf; exact ⟨ c * 2, mul_pos hc zero_lt_two, a, fun n hn ↦ by nlinarith [ ha n hn, h_ceil n ] ⟩ ;
    · intro hf;
      rw [ Asymptotics.isBigO_iff ] at *;
      obtain ⟨ c, hc ⟩ := hf;
      norm_num [ Norm.norm ] at *;
      exact ⟨ c * 2, hc.choose, fun n hn ↦ by nlinarith [ hc.choose_spec n hn, h_ceil n, Real.exp_pos n, Nat.le_ceil ( Real.exp n ) ] ⟩;
  exact h_const_mul f

theorem exp_iff_rpow {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ C ^ x : ℕ → ℝ) := by
  constructor;
  · rintro ⟨C, hC⟩
    use C
    simpa [Asymptotics.isBigO_iff] using hC
  · -- If there exists a real number $C$ such that $f(n) = O(C^n)$, then there exists a natural number $n$ such that $f(n) = O(n^n)$.
    rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (fun x ↦ (f x : ℝ)) =O[Filter.atTop] (fun x ↦ (n : ℝ) ^ x) := by
      use ⌈|C|⌉₊
      apply hC.trans
      rw [Asymptotics.isBigO_iff]
      norm_num
      exact ⟨1, 0, fun n hn ↦ by grw [one_mul, ← Nat.le_ceil]⟩
    -- Since $n$ is a natural number, we can use it directly as the exponent in the exponential growth rate.
    use n
    simpa [Asymptotics.isBigO_iff'] using hn

theorem exp_iff_rexp_mul {f : ℕ → ℕ} : f ∈ exp ↔
    ∃ C, (f · : ℕ → ℝ) =O[.atTop] (fun x ↦ Real.exp (C * x) : ℕ → ℝ) := by
  rw [exp_iff_rpow];
  constructor <;> rintro ⟨ C, hC ⟩;
  · use Real.log ( |C| + 1 );
    refine' hC.trans _;
    rw [ Asymptotics.isBigO_iff ];
    simp +zetaDelta at *;
    exact ⟨ 1, 0, fun n hn ↦ by rw [ Real.exp_mul, Real.exp_log ( by positivity ) ] ; norm_num; exact pow_le_pow_left₀ ( by positivity ) ( by linarith [ abs_nonneg C ] ) _ ⟩;
  · use Real.exp C;
    simpa [ Real.exp_mul ] using hC

end equivalent_defs

section closure_mul

variable {f g : ℕ → ℕ}

theorem polylog_mul (hf : f ∈ polylog) (hg : g ∈ polylog) : (f * g) ∈ polylog := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a + b
  convert ha.mul hb
  simp [pow_add]

theorem linear_of_sqrt_mul_sqrt (hf : f ∈ sqrt) (hg : g ∈ sqrt) : (f * g) ∈ linear := by
  convert (hf.mul hg).trans ?_
  rw [ Asymptotics.isBigO_iff' ]
  simp
  exact ⟨ 1, by norm_num, 0, fun b hb ↦ by
    norm_cast; nlinarith [ Nat.sqrt_le b ] ⟩

theorem linearithmic_of_linear_mul_log (hf : f ∈ linear) (hg : g ∈ log) : (f * g) ∈ linearithmic := by
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
  -- Let $C = a + b$. Then we have $(fun x ↦ ((f x) * (g x)) : ℝ)$ is $O[Filter.atTop] ((fun n ↦ (2 : ℝ) ^ ((Nat.log 2 n) ^ C) : ℕ → ℝ))$.
  use a + b
  convert (ha.mul hb).trans ?_
  norm_num [Asymptotics.isBigO_iff, Norm.norm]
  use 2, 2, fun k hk ↦ ?_
  rw [← pow_succ', Nat.pow_add, ← pow_add]
  exact pow_le_pow_right₀ one_le_two ( by nlinarith [ pow_pos ( show Nat.log 2 k > 0 from Nat.log_pos ( by norm_num ) hk ) a, pow_pos ( show Nat.log 2 k > 0 from Nat.log_pos ( by norm_num ) hk ) b ] );

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
    exact ⟨ h_exp_log.choose, fun n hn ↦ by simpa only [ pow_add, mul_assoc ] using le_trans ( h_exp_log.choose_spec n hn ) ( Nat.le_ceil _ ) ⟩;
  -- By dividing both sides of the inequality by $2^b$, we reduce it to showing that $c₂ * 2 ^ ((log2 b) ^ C) ≤ \exp(b - b \cdot \log_2(e))$.
  suffices h₂ : ∃ k : ℕ, ∀ b ≥ k, (c₂ * 2 ^ ((Nat.log 2 b) ^ C)) ≤ (Real.exp (b * (1 - Real.log 2))) by
    rcases h₂ with ⟨k, hk⟩
    use k; intro b hb; rw [ pow_add ] ; rw [ ← mul_comm ] ; specialize hk b hb; convert mul_le_mul_of_nonneg_left hk <| pow_nonneg zero_le_two b using 1 ;
    · ring
    · rw [ mul_sub, mul_one, Real.exp_sub ];
      norm_num [ Real.exp_neg, Real.exp_nat_mul, Real.exp_log, mul_div_cancel₀ ];
  -- We'll use that exponential functions grow faster than polynomial functions. Specifically, we'll find a $k$ such that for all $b \geq k$, $2^{(\log_2(b))^C}$ is dominated by $e^{b (1 - \log(2))}$.
  suffices h_exp_poly : Filter.Tendsto (fun b : ℕ ↦ (2 ^ ((Nat.log 2 b) ^ C) : ℝ) / Real.exp (b * (1 - Real.log 2))) Filter.atTop (nhds 0) by
    have := h_exp_poly.eventually ( gt_mem_nhds <| show 0 < c₂⁻¹ by positivity )
    rw [Filter.eventually_atTop] at this
    peel this with _ n _ this
    rw [ div_lt_iff₀ ( Real.exp_pos _ ) ] at this
    nlinarith [ Real.exp_pos ( n * ( 1 - Real.log 2 ) ), inv_mul_cancel₀ ( ne_of_gt hc₂ ) ]
  -- Let $y = \log_2(b)$, therefore the expression becomes $\lim_{y \to \infty} \frac{2^{y^C}}{e^{2^y (1 - \log(2))}}$.
  suffices h_log : Filter.Tendsto (fun y : ℕ ↦ (2 ^ (y ^ C) : ℝ) / Real.exp (2 ^ y * (1 - Real.log 2))) Filter.atTop (nhds 0) by
    refine' squeeze_zero_norm' _ ( h_log.comp ( _ ) );
    case refine'_2 => use fun x ↦ Nat.log 2 x;
    -- Case 1
    · simp only [norm_div, norm_pow, Real.norm_ofNat, Real.norm_eq_abs, Real.abs_exp, Function.comp_apply,
        Filter.eventually_atTop, ge_iff_le]
      refine' ⟨ 4, fun n hn ↦ _ ⟩;
      gcongr;
      -- Case 1
      · linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
      -- Case 2
      · exact_mod_cast Nat.pow_log_le_self 2 <| by linarith;
    -- Case 2
    · rw [ Filter.tendsto_atTop_atTop ];
      exact fun b ↦ ⟨ 2 ^ b, fun a ha ↦ Nat.le_log_of_pow_le ( by norm_num ) ha ⟩;
  -- Taking the natural logarithm of the expression inside the limit, we get $\lim_{y \to \infty} (y^C \ln(2) - 2^y (1 - \ln(2)))$.
  suffices h_ln : Filter.Tendsto (fun y : ℕ ↦ y ^ C * Real.log 2 - 2 ^ y * (1 - Real.log 2)) Filter.atTop Filter.atBot by
    -- If the natural logarithm of the expression tends to $-\infty$, then the expression tends to $0$.
    have h_exp_ln : Filter.Tendsto (fun y : ℕ ↦ Real.exp (y ^ C * Real.log 2 - 2 ^ y * (1 - Real.log 2))) Filter.atTop (nhds 0) := by
      aesop;
    convert h_exp_ln using 1;
    norm_num [ Real.exp_sub, Real.exp_nat_mul, Real.exp_log ];
    exact funext fun x ↦ by
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ]
      norm_num [mul_comm]
  -- We'll use that exponential functions grow faster than polynomial functions under the given conditions.
  have h_exp_poly : Filter.Tendsto (fun y : ℕ ↦ (2 : ℝ) ^ y / y ^ C) Filter.atTop Filter.atTop := by
    -- Recognize that this is a special case of the exponential function $a^x / x^C$ where $a = 2$.
    suffices h_exp : Filter.Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log 2) / x ^ C) Filter.atTop Filter.atTop by
      convert h_exp.comp tendsto_natCast_atTop_atTop using 2 ; norm_num [ Real.exp_nat_mul, Real.exp_log ];
    -- Let $y = x \log 2$, therefore the limit becomes $\lim_{y \to \infty} \frac{e^y}{y^C}$.
    suffices h_limit_y : Filter.Tendsto (fun y : ℝ ↦ Real.exp y / y ^ C) Filter.atTop Filter.atTop by
      have h_subst : Filter.Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log 2) / (x * Real.log 2) ^ C) Filter.atTop Filter.atTop := by
        exact h_limit_y.comp <| Filter.tendsto_id.atTop_mul_const <| Real.log_pos <| by norm_num;
      -- We simplify the expression $\frac{e^{x \ln 2}}{(x \ln 2)^C}$ to $\frac{e^{x \ln 2}}{x^C (\ln 2)^C}$.
      have h_simplify : Filter.Tendsto (fun x : ℝ ↦ Real.exp (x * Real.log 2) / x ^ C / (Real.log 2) ^ C) Filter.atTop Filter.atTop := by
        simpa only [ mul_pow, div_div ] using h_subst;
      convert h_simplify.atTop_mul_const ( pow_pos ( Real.log_pos one_lt_two ) C ) using 2
      ring_nf
      norm_num [ mul_assoc, mul_comm, mul_left_comm ]
    exact Real.tendsto_exp_div_pow_atTop _;
  -- Rewrite the limit expression using the property of limits: $\lim_{y \to \infty} (y^C \ln(2) - 2^y (1 - \ln(2))) = \lim_{y \to \infty} y^C (\ln(2) - \frac{2^y (1 - \ln(2))}{y^C})$.
  have h_rewrite : Filter.Tendsto (fun y : ℕ ↦ (y ^ C : ℝ) * (Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C)) Filter.atTop Filter.atBot := by
    -- Since $\frac{2^y (1 - \ln(2))}{y^C}$ tends to infinity, $\ln(2) - \frac{2^y (1 - \ln(2))}{y^C}$ tends to $-\infty$.
    have h_ln_tendsto : Filter.Tendsto (fun y : ℕ ↦ Real.log 2 - (2 ^ y * (1 - Real.log 2)) / y ^ C) Filter.atTop Filter.atBot := by
      -- Since $1 - \ln(2)$ is positive, multiplication by $(1 - \ln(2))$ preserves the limit.
      have h_mul : Filter.Tendsto (fun y : ℕ ↦ (2 ^ y * (1 - Real.log 2)) / y ^ C) Filter.atTop Filter.atTop := by
        simpa only [ mul_div_right_comm ] using h_exp_poly.atTop_mul_const ( sub_pos.mpr <| Real.log_two_lt_d9.trans_le <| by norm_num );
      rw [ Filter.tendsto_atTop_atBot ];
      exact fun x ↦ Filter.eventually_atTop.mp ( h_mul.eventually_gt_atTop ( Real.log 2 - x ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ by linarith [ hN n hn ] ⟩;
    rw [ Filter.tendsto_atTop_atBot ] at *;
    intro b;
    obtain ⟨ i, hi ⟩ := h_ln_tendsto ( Min.min b 0 );
    exact ⟨ i + 1, fun j hj ↦ le_trans ( mul_le_mul_of_nonneg_left ( hi _ ( by linarith ) ) ( by positivity ) ) <|
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

end closure_mul

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
    have h_limit : Filter.Tendsto (fun x : ℝ ↦ (Real.logb 2 x) ^ k / Real.sqrt x) Filter.atTop (nhds 0) := by
      -- Let `y = log₂ x`, therefore the expression becomes `(y ^ k) / Real.sqrt (2 ^ y)`.
      suffices h_subst : Filter.Tendsto (fun y : ℝ ↦ y ^ k / Real.sqrt (2 ^ y)) Filter.atTop (nhds 0) by
        exact (h_subst.comp ( Real.tendsto_logb_atTop one_lt_two)).congr' (by
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx
          simp [ Real.sqrt_eq_rpow, Real.rpow_logb, hx ] );
      -- We'll use the exponential property: $\sqrt{2^y} = 2^{y/2}$.
      suffices h_exp : Filter.Tendsto (fun y : ℝ ↦ y ^ k / 2 ^ (y / 2)) Filter.atTop (nhds 0) by
        convert h_exp using 3
        rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by norm_num ) ]
        ring_nf
      -- Let `z = y / 2`, therefore the expression becomes `(2z)^k / e^{z * Real.log 2} = 2^k * z^k / e^{z * Real.log 2}`.
      suffices h_z : Filter.Tendsto (fun z : ℝ ↦ (2 ^ k : ℝ) * z ^ k / Real.exp (z * Real.log 2)) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const <| show ( 2 : ℝ ) ⁻¹ > 0 by positivity ) using 2
        norm_num
        ring_nf
        simp [ Real.rpow_def_of_pos, mul_assoc, mul_left_comm (Real.log 2) ]
      -- We'll use the fact that $Real.exp (z * Real.log 2)$ grows much faster than $z^k$ for any $k$.
      have h_exp_growth : Filter.Tendsto (fun z : ℝ ↦ z ^ k / Real.exp (z * Real.log 2)) Filter.atTop (nhds 0) := by
        -- Let $y = z \log 2$, therefore the expression becomes $\frac{(y / \log 2)^k}{e^y}$.
        suffices h_subst'' : Filter.Tendsto (fun y : ℝ ↦ (y / Real.log 2) ^ k / Real.exp y) Filter.atTop (nhds 0) by
          convert h_subst''.comp ( Filter.tendsto_id.atTop_mul_const <| Real.log_pos one_lt_two ) using 2 ; norm_num
        -- We'll use the fact that $Real.exp y$ grows much faster than $y^k$.
        have h_exp_y_growth : Filter.Tendsto (fun y : ℝ ↦ y ^ k / Real.exp y) Filter.atTop (nhds 0) := by
          simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
        convert h_exp_y_growth.div_const ( Real.log 2 ^ k ) using 2 <;> ring;
      simpa [ mul_div_assoc ] using h_exp_growth.const_mul _;
    have := h_limit.eventually ( gt_mem_nhds <| show 0 < c⁻¹ from inv_pos.mpr hc₀ );
    simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
    obtain ⟨w, h⟩ := hfc
    obtain ⟨a, h_1⟩ := this
    exact ⟨a ⊔ 2, fun x hx ↦ by
      have := h_1 x ( le_trans ( le_max_left _ _ ) hx ) ;
      have h₂ : 0 < x := by linarith [le_max_left a 2, le_max_right a 2]
      rw [ div_lt_iff₀ (by positivity) ] at this
      nlinarith [ le_max_right a 2, Real.sqrt_nonneg x, inv_mul_cancel₀ <| ne_of_gt hc₀,
        Real.sq_sqrt h₂.le ] ⟩;
  -- Let $x \geq \max(N, M)$.
  obtain ⟨w_1, h_1⟩ : ∃ K, ∀ x ≥ K, f x ≤ Real.sqrt x :=
    ⟨⌈M⌉₊ + N, fun x hx ↦ (hN x (by linarith)).trans
        ( by simpa using hM x (( Nat.le_ceil _ ).trans ( mod_cast by linarith ) ) ) ⟩
  simp_all only [gt_iff_lt, Int.norm_natCast, Nat.cast_pow, norm_pow, Filter.eventually_atTop, ge_iff_le]
  apply Asymptotics.isBigO_iff.mpr
  use 1
  norm_num;
  exact ⟨ w_1 + 1, fun b hb ↦ Nat.le_sqrt.mpr <| by
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
    have h_log_growth : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / Real.sqrt n) Filter.atTop (nhds 0) := by
      -- We'll use that logarithmic base 2 grows slower than any polynomial function under the real numbers, so that for large $n$, $(\log_2(n))^C$ is much smaller than $\sqrt{n}$.
      have h_log_growth : Filter.Tendsto (fun x : ℝ ↦ (Real.log x / Real.log 2) ^ C / Real.sqrt x) Filter.atTop (nhds 0) := by
        -- Let $y = \log_2(x)$. Then we can rewrite our limit in terms of $y$:
        suffices h_log_growth_y : Filter.Tendsto (fun y : ℝ ↦ y ^ C / Real.sqrt (2 ^ y)) Filter.atTop (nhds 0) by
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
        suffices h_log_growth_y_simplified : Filter.Tendsto (fun y : ℝ ↦ y ^ C / Real.exp (y * Real.log 2 / 2)) Filter.atTop (nhds 0) by
          convert h_log_growth_y_simplified using 2 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ] ;
          ring_nf
          rw [ ← Real.exp_mul ];
        -- Let $z = \frac{y \log 2}{2}$, so we can rewrite the limit as $\lim_{z \to \infty} \frac{(\frac{2z}{\log 2})^C}{e^z}$.
        suffices h_log_growth_z : Filter.Tendsto (fun z : ℝ ↦ ((2 * z) / Real.log 2) ^ C / Real.exp z) Filter.atTop (nhds 0) by
          have h_log_growth_z : Filter.Tendsto (fun y : ℝ ↦ ((2 * (y * Real.log 2 / 2)) / Real.log 2) ^ C / Real.exp (y * Real.log 2 / 2)) Filter.atTop (nhds 0) := by
            exact h_log_growth_z.comp ( Filter.Tendsto.atTop_mul_const ( by positivity ) <| Filter.tendsto_id.atTop_mul_const <| by positivity );
          convert h_log_growth_z using 3 ;
          ring_nf
          norm_num
        -- Now consider the term $(\frac{2z}{\log 2})^C / e^z$. We want to show that this goes to $0$ as $z \to \infty$.
        suffices h_term : Filter.Tendsto (fun z : ℝ ↦ z ^ C / Real.exp z) Filter.atTop (nhds 0) by
          convert h_term.const_mul ( ( Real.log 2 ) ⁻¹ ^ C * 2 ^ C ) using 2 <;> ring;
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C;
      refine' squeeze_zero_norm' _ ( h_log_growth.comp tendsto_natCast_atTop_atTop );
      refine' Filter.eventually_atTop.mpr ⟨ 2, fun n hn ↦ _ ⟩ ; rw [ Function.comp_apply, Real.norm_of_nonneg ( by positivity ) ] ; gcongr;
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
  use fun n ↦ Nat.sqrt n * Nat.log 2 n;
  simp_all only [Nat.cast_mul]
  apply And.intro
  · refine' Asymptotics.isLittleO_iff.2 fun ε hε ↦ _;
    -- We'll use that $\log_2 x$ grows slower than any polynomial function, specifically $x^{1/2}$.
    have h_log_growth : Filter.Tendsto (fun x : ℕ ↦ (Nat.log 2 x : ℝ) / Real.sqrt x) Filter.atTop (nhds 0) := by
      -- We can use the change of variables $u = \log_2 x$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ ↦ u / 2^(u/2)) Filter.atTop (nhds 0) by
        have h_log : Filter.Tendsto (fun x : ℕ ↦ (Nat.log 2 x : ℝ) / 2^(Nat.log 2 x / 2 : ℝ)) Filter.atTop (nhds 0) := by
          exact h_log.comp ( tendsto_natCast_atTop_atTop.comp ( Filter.tendsto_atTop_atTop.mpr fun n ↦ ⟨ 2 ^ n, fun x hx ↦ Nat.le_log_of_pow_le ( by norm_num ) hx ⟩ ) );
        refine' squeeze_zero_norm' _ h_log
        simp_all only [norm_div, RCLike.norm_natCast, Real.norm_eq_abs, Filter.eventually_atTop, ge_iff_le]
        refine' ⟨ 2, fun n hn ↦ _ ⟩ ; rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; gcongr;
        rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> norm_num;
        · have := Real.log_le_log ( by positivity ) ( show ( n : ℝ ) ≥ 2 ^ Nat.log 2 n by exact_mod_cast Nat.pow_log_le_self 2 ( by positivity ) ) ; norm_num at * ; nlinarith [ Real.log_pos one_lt_two ];
        · linarith;
      -- We can use the fact that $2^{u/2} = e^{u \ln 2 / 2}$ and apply the exponential function to both the numerator and the denominator.
      suffices h_exp : Filter.Tendsto (fun u : ℝ ↦ u / Real.exp (u * Real.log 2 / 2)) Filter.atTop (nhds 0) by
        convert h_exp using 2 ; norm_num [ Real.rpow_def_of_pos ]
        ring_nf
      -- Let $y = \frac{u \ln 2}{2}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{2y}{e^y}$.
      suffices h_y : Filter.Tendsto (fun y : ℝ ↦ 2 * y / Real.exp y) Filter.atTop (nhds 0) by
        have := h_y.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < Real.log 2 / 2 by positivity ) );
        convert this.div_const ( Real.log 2 ) using 2 <;> norm_num
        ring_nf
        norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      simpa [ mul_div_assoc, Real.exp_neg ] using Filter.Tendsto.const_mul 2 ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
    have := h_log_growth.eventually ( gt_mem_nhds <| show 0 < ε by positivity )
    simp_all only [Filter.eventually_atTop, ge_iff_le, norm_mul, norm_natCast]
    obtain ⟨w, h⟩ := this
    refine' ⟨ w + 1, fun n hn ↦ _ ⟩
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
    have h_log_growth : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) - x) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_add_const_right _ _ ( tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun n ↦ ⟨ 2 ^ n, fun m hm ↦ Nat.le_log_of_pow_le ( by norm_num ) hm ⟩ );
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

theorem linear_subset_linearithmic : linear ⊆ linearithmic := by
  refine' fun _ h ↦ h.trans _
  norm_num [Asymptotics.isBigO_iff]
  refine ⟨1, 2, fun n hn ↦ ?_⟩
  rw [one_mul]
  exact_mod_cast Nat.le_mul_of_pos_right n (Nat.log_pos one_lt_two hn)

theorem linear_ssubset_linearithmic : linear ⊂ linearithmic := by
  use linear_subset_linearithmic
  simp [linear, linearithmic, bigO]
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

theorem linearithmic_subset_quasilinear : linearithmic ⊆ quasilinear :=
  fun _ _ ↦ ⟨1, by simpa⟩

theorem linearithmic_ssubset_quasilinear : linearithmic ⊂ quasilinear := by
  use linearithmic_subset_quasilinear
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
  refine' ⟨ 1, 2, fun n hn ↦ _ ⟩ ; norm_num;
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
    have h_exp_poly : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * (Nat.log 2 n : ℝ) ^ x / (n : ℝ) ^ 2) Filter.atTop (nhds 0) := by
      -- We can simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ x / (n : ℝ)) Filter.atTop (nhds 0) by
        refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ div_eq_div_iff ] <;> ring_nf <;> positivity );
      -- Let $y = \log_2 n$, therefore the expression becomes $\frac{y^x}{2^y}$.
      suffices h_log : Filter.Tendsto (fun y : ℕ ↦ (y : ℝ) ^ x / (2 ^ y)) Filter.atTop (nhds 0) by
        have h_subst : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ x / (2 ^ (Nat.log 2 n))) Filter.atTop (nhds 0) := by
          exact h_log.comp ( Filter.tendsto_atTop_atTop.mpr fun n ↦ ⟨ 2 ^ n, fun m hm ↦ Nat.le_log_of_pow_le ( by norm_num ) hm ⟩ );
        refine' squeeze_zero_norm' _ h_subst;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn
        rw [ Real.norm_of_nonneg ( by positivity ) ]
        gcongr
        norm_cast
        exact Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hn)
      -- We can convert this limit into a form that is easier to handle by substituting $z = y \log 2$.
      suffices h_log : Filter.Tendsto (fun z : ℝ ↦ z ^ x / Real.exp z) Filter.atTop (nhds 0) by
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
    specialize ha ( 2 ^ m ) ( Nat.le_of_lt ( Nat.lt_of_lt_of_le hm.1 ( Nat.le_of_lt ( Nat.recOn m ( by norm_num ) fun n ihn ↦ by norm_num [ Nat.pow_succ ] at * ; linarith ) ) ) )
    norm_num [ Norm.norm ] at ha
    exact ha.not_gt <| mod_cast hm.2

lemma polylog_is_littleO_sqrt {f : ℕ → ℕ} (hf : f ∈ GrowthRate.polylog) :
    (fun n ↦ (f n : ℝ)) =o[.atTop] (fun n ↦ Real.sqrt n) := by
  have h_log_poly : ∀ w : ℕ, (fun n ↦ (Nat.log 2 n : ℝ) ^ w) =o[Filter.atTop] (fun n ↦ Real.sqrt n) := by
    intro w
    have h_log_poly_aux : Filter.Tendsto (fun n ↦ (Real.log n / Real.log 2) ^ w / Real.sqrt n) Filter.atTop (nhds 0) := by
      -- We can simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n ↦ (Real.log n) ^ w / Real.sqrt n) Filter.atTop (nhds 0) by
        convert h_simplify.div_const ( Real.log 2 ^ w ) using 2 <;> ring;
      -- Let $y = \log x$, therefore the expression becomes $\frac{y^w}{e^{y/2}}$.
      suffices h_log : Filter.Tendsto (fun y ↦ y ^ w / Real.exp (y / 2)) Filter.atTop (nhds 0) by
        have := h_log.comp ( Real.tendsto_log_atTop );
        apply this.congr'
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx
        rw [ Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ]
        ring_nf
      -- Let $z = \frac{y}{2}$, therefore the limit becomes $\lim_{z \to \infty} \frac{(2z)^w}{e^z}$.
      suffices h_z : Filter.Tendsto (fun z ↦ (2 * z) ^ w / Real.exp z) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) using 2
        norm_num
        ring_nf
      -- We can factor out the constant $2^w$ from the limit.
      suffices h_factor : Filter.Tendsto (fun z ↦ z ^ w / Real.exp z) Filter.atTop (nhds 0) by
        convert h_factor.const_mul ( 2 ^ w ) using 2 <;> ring;
      simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero w;
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · have h_log_poly_aux : Filter.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ w / Real.sqrt n) Filter.atTop (nhds 0) := by
        have : ∀ n : ℕ, n ≥ 2 → (Nat.log 2 n : ℝ) ^ w / Real.sqrt n ≤ (Real.log n / Real.log 2) ^ w / Real.sqrt n := by
          intro n hn; gcongr;
          rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ), ← Real.log_pow ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self _ ( by positivity ) )
        exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun n hn ↦ by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact this n hn ⟩ ) ( h_log_poly_aux.comp tendsto_natCast_atTop_atTop );
      convert h_log_poly_aux using 1;
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hx;
  rcases hf with ⟨w, hw⟩
  have h_log_poly : (fun n ↦ (f n : ℝ)) =O[Filter.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ w) := by
    rw [ Asymptotics.isBigO_iff ] at *;
    aesop;
  exact h_log_poly.trans_isLittleO ( by aesop )

theorem quasipoly_subset_two_pow : quasipoly ⊆ two_pow := by
  rintro f ⟨ C, hC ⟩;
  have h_exp : (fun n ↦ 2 ^ (Nat.log 2 n ^ C) : ℕ → ℤ) =O[Filter.atTop] (fun n ↦ 2 ^ n : ℕ → ℤ) := by
    have h_exp : ∀ᶠ n in Filter.atTop, (Nat.log 2 n ^ C : ℕ) ≤ n := by
      have h_log : Filter.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C / n) Filter.atTop (nhds 0) := by
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$.
        suffices h_log_growth : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / (2 ^ m : ℝ)) Filter.atTop (nhds 0) by
          have h_log_growth : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / (2 ^ (Nat.log 2 n) : ℝ)) Filter.atTop (nhds 0) := by
            exact h_log_growth.comp ( Filter.tendsto_atTop_atTop.mpr fun m ↦ ⟨ 2 ^ m, fun n hn ↦ Nat.le_log_of_pow_le ( by norm_num ) hn ⟩ );
          refine' squeeze_zero_norm' _ h_log_growth;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn
          rw [ Real.norm_of_nonneg ( by positivity ) ]
          gcongr
          norm_cast
          exact Nat.pow_log_le_self 2 hn.ne'
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$ and using the fact that $2^m$ grows exponentially.
        suffices h_log_growth : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) by
          simpa [ Real.exp_nat_mul, Real.exp_log ] using h_log_growth;
        -- Let $y = m \log 2$, therefore the limit becomes $\lim_{y \to \infty} \frac{y^C}{e^y}$.
        suffices h_log_growth : Filter.Tendsto (fun y : ℝ ↦ y ^ C / Real.exp y) Filter.atTop (nhds 0) by
          have h_log_growth : Filter.Tendsto (fun m : ℕ ↦ (m * Real.log 2 : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) := by
            exact h_log_growth.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos one_lt_two;
          convert h_log_growth.div_const ( Real.log 2 ^ C ) using 2 <;> ring_nf
          norm_num [ Real.exp_ne_zero ] ;
          exact eq_div_of_mul_eq ( by positivity ) ( by ring );
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C;
      filter_upwards [ h_log.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ div_lt_one ( by positivity ) ] at hn; exact_mod_cast hn.le;
    rw [ Asymptotics.isBigO_iff ];
    norm_num +zetaDelta at *;
    exact ⟨ 1, h_exp.choose, fun n hn ↦ by rw [ one_mul ] ; exact pow_le_pow_right₀ ( by norm_num [ Norm.norm ] ) ( h_exp.choose_spec n hn ) ⟩;
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
  have h_exp_growth : Filter.Tendsto (fun n ↦ (2 : ℝ) ^ (Nat.log 2 n ^ C) / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    -- We can rewrite the limit expression using the properties of exponents: $2^{(\log n)^C} / 2^n = 2^{(\log n)^C - n}$.
    suffices h_exp : Filter.Tendsto (fun n ↦ (2 : ℝ) ^ ((Nat.log 2 n) ^ C - n : ℝ)) Filter.atTop (nhds 0) by
      convert h_exp using 2 ; norm_num [ Real.rpow_sub ];
      norm_cast;
    -- We'll use that $(\log n)^C - n$ tends to $-\infty$ as $n$ tends to $\infty$.
    have h_log : Filter.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C - n) Filter.atTop Filter.atBot := by
      -- We'll use that $(\log n)^C$ grows much slower than $n$.
      have h_log_growth : Filter.Tendsto (fun n ↦ (Nat.log 2 n : ℝ) ^ C / n) Filter.atTop (nhds 0) := by
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$.
        suffices h_log : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / (2 ^ m)) Filter.atTop (nhds 0) by
          have h_log : Filter.Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ) ^ C / (2 ^ (Nat.log 2 n))) Filter.atTop (nhds 0) := by
            exact h_log.comp ( Filter.tendsto_atTop_atTop.mpr fun m ↦ ⟨ 2 ^ m, fun n hn ↦ Nat.le_log_of_pow_le ( by norm_num ) hn ⟩ );
          refine' squeeze_zero_norm' _ h_log;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; norm_cast ; exact Nat.pow_log_le_self 2 hn.ne';
        -- We can convert this limit into a form that is easier to handle by substituting $m = \log_2 n$. We'll use the fact that $2^m$ grows much faster than $m^C$.
        have h_log : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) := by
          -- Let $y = m \log 2$, therefore the limit becomes $\lim_{y \to \infty} \frac{y^C}{e^y}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ ↦ y ^ C / Real.exp y) Filter.atTop (nhds 0) by
            have h_subst : Filter.Tendsto (fun m : ℕ ↦ (m * Real.log 2 : ℝ) ^ C / Real.exp (m * Real.log 2)) Filter.atTop (nhds 0) := by
              exact h_log.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos one_lt_two;
            convert h_subst.div_const ( Real.log 2 ^ C ) using 2
            · ring_nf
              norm_num [ mul_right_comm, mul_assoc, mul_left_comm, ne_of_gt, Real.log_pos ];
            · simp
          simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero C;
        simpa [ Real.exp_nat_mul, Real.exp_log ] using h_log;
      -- We can rewrite the limit expression using the properties of limits.
      have h_rewrite : Filter.Tendsto (fun n ↦ ((Nat.log 2 n : ℝ) ^ C / n - 1) * n) Filter.atTop Filter.atBot := by
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
  exact absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds ( h_exp_growth.const_mul c ) <| Filter.eventually_atTop.mpr ⟨ a, fun n hn ↦ by simpa [ mul_div_assoc ] using h_div n hn ⟩ ) ( by norm_num )

theorem two_pow_subset_e_pow : two_pow ⊆ e_pow := by
  -- We'll use the fact that $e \approx 2.718$ to show that $2^n$ is bounded above by $e^n$.
  have h_exp_bound : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (Real.exp n) := by
    intro n;
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
    exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( Real.log_two_lt_d9.le.trans ( by norm_num ) );
  -- By definition of big O, if $2^n \leq e^n$ for all $n$, then $2^n$ is $O(e^n)$.
  have h_two_pow_e_pow : (2 ^ · : ℕ → ℕ) ∈ bigO (fun n ↦ ⌈Real.exp n⌉₊ : ℕ → ℕ) := by
    refine' Asymptotics.isBigO_iff.mpr _;
    -- Choose $c = 1$.
    use 1;
    exact Filter.eventually_atTop.mpr ⟨ 0, fun n hn ↦ by erw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; exact_mod_cast Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( Real.exp n ), h_exp_bound n ] ⟩;
  -- Since `two_pow` is defined as `bigO (fun n ↦ 2 ^ n)`, and we have shown that `(fun n ↦ 2 ^ n) ∈ bigO (fun n ↦ ⌈Real.exp n⌉₊)`, it follows that `two_pow ⊆ e_pow`.
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
  have h_exp_growth : Filter.Tendsto (fun n : ℕ ↦ (Real.exp n : ℝ) / 2 ^ n) Filter.atTop Filter.atTop := by
    -- We can rewrite the limit expression using the fact that $e^n / 2^n = (e/2)^n$.
    suffices h_exp_growth : Filter.Tendsto (fun n : ℕ ↦ (Real.exp 1 / 2 : ℝ) ^ n) Filter.atTop Filter.atTop by
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
  have h_exp : Filter.Tendsto (fun x : ℕ ↦ (3 ^ x : ℝ) / ⌈(Real.exp x)⌉₊) Filter.atTop Filter.atTop := by
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
  have hf_growth : Filter.Tendsto (fun n ↦ (y * (c ^ n) : ℝ) / n.factorial) Filter.atTop (nhds 0) := by
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
        suffices h_poly : Nat.Primrec (fun n ↦ c * n) by
          exact h_poly.comp hx
        convert Nat.Primrec.mul.comp ((Nat.Primrec.const c).pair Nat.Primrec.id) using 2
        norm_num [Nat.unpaired]
      exact ⟨m, fun n hn ↦ by simpa using (hm n).trans_le (ack_le_ack hn le_rfl)⟩
    simp only [norm_natCast, Filter.eventually_atTop, not_exists, not_and, not_forall, not_le]
    intro c hc n
    obtain ⟨N, hN⟩ := h_ineq (⌈c⌉₊) (Nat.ceil_pos.mpr hc)
    use n + N, by omega
    grw [Nat.le_ceil c]
    exact_mod_cast hN _ (by omega)

end ordering

section closure_comp

variable {f g : ℕ → ℕ}

/--
If a function $g$ is polynomially bounded, then $\log(g(n))$ is $O(\log n)$.
-/
private lemma isBigO_log_comp_poly_real {C : ℝ} (hg : (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ C)) :
    (fun n ↦ Real.log (g n)) =O[.atTop] (Real.log ·) := by
  rw [Asymptotics.isBigO_iff'] at hg ⊢
  obtain ⟨c, hc₀, hc⟩ := hg
  use |C| + 1, by positivity
  filter_upwards [ hc, Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ⌈c⌉₊ ] with x hx₁ hx₂ hx₃
  by_cases hx₄ : g x = 0 <;> simp_all
  · positivity
  · rw [
      abs_of_nonneg (Real.log_nonneg <| mod_cast Nat.one_le_iff_ne_zero.mpr hx₄),
      abs_of_nonneg (Real.log_nonneg <| mod_cast hx₂.le) ]
    have h := Real.log_le_log (by positivity) hx₁
    rw [ Real.log_mul (by positivity) (by positivity), Real.log_abs, Real.log_rpow (by positivity) ] at h
    cases abs_cases C <;>
    nlinarith [@Real.log_nonneg x (by norm_cast; linarith), @Real.log_le_log c x (by positivity) ((Nat.le_ceil _).trans (mod_cast hx₃.le))]

theorem log_comp_poly (hf : f ∈ log) (hg : g ∈ poly) : f ∘ g ∈ log := by
  -- Apply `poly_iff_rpow` on `hg` to get a constant `C` such that `g n =O n^C`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ C) :=
    poly_iff_rpow.mp hg
  -- Apply `GrowthRate.isBigO_log_comp_poly_real` to `hC` to deduce that `Real.log (g n) =O Real.log n`.
  have h_log_g : (fun n ↦ Real.log (g n)) =O[.atTop] (Real.log ·) :=
    isBigO_log_comp_poly_real hC
  -- Since `f` is bounded by `A + B * Real.log x` for all `x`, we have `f (g n) ≤ A + B * Real.log (g n)` for large `g n`.
  have h_f_g : ∃ A B : ℝ, ∀ n, f (g n) ≤ A + B * Real.log (g n) := by
    -- By definition of `GrowthRate.log`, there exist constants `A` and `B` such that `f x ≤ A + B * Real.log x` for all `x`.
    obtain ⟨A, B, hAB⟩ : ∃ A B : ℝ, ∀ x : ℕ, x ≥ 1 → f x ≤ A + B * Real.log x := by
      have h_f_g : (fun x : ℕ ↦ (f x : ℝ)) =O[.atTop] (Real.log ·) := by
        exact log_iff_rlog.mp hf;
      rw [ Asymptotics.isBigO_iff ] at h_f_g;
      norm_num +zetaDelta at *;
      obtain ⟨ c, a, hc ⟩ := h_f_g;
      use ( ∑ x ∈ Finset.range ( a + 1 ), f x ) + |c|, |c|;
      intro x hx; by_cases hx' : x ≤ a <;> simp_all
      · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( Finset.single_le_sum ( fun x _ ↦ Nat.cast_nonneg ( f x ) ) ( Finset.mem_range.mpr ( by linarith ) ) ) ( abs_nonneg _ ) ) ( mul_nonneg ( abs_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hx ) ) );
      · cases abs_cases c <;> cases abs_cases ( Real.log x ) <;> nlinarith [ hc x hx'.le, Real.log_nonneg ( show ( x : ℝ ) ≥ 1 by norm_cast ), show ( ∑ i ∈ Finset.range ( a + 1 ), ( f i : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _ ];
    exact ⟨ Max.max A ( f 0 ), Max.max B 0, fun n ↦ if hn : 1 ≤ g n then hAB _ hn |> le_trans <| by gcongr <;> norm_num else by aesop ⟩;
  -- Since `Real.log (g n) =O Real.log n`, by transitivity `f (g n) =O Real.log n`.
  obtain ⟨A, B, hAB⟩ := h_f_g;
  have h_trans : (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (Real.log ·) := by
    -- Since $A$ is a constant, it is $O(1)$, and since $B * \log(g(n))$ is $O(\log(n))$, their sum is $O(\log(n))$.
    have h_const : (fun n ↦ A : ℕ → ℝ) =O[.atTop] (Real.log ·) := by
      norm_num [ Asymptotics.isBigO_iff ];
      exact ⟨ |A|, 3, fun n hn ↦ by rw [ abs_of_nonneg ( Real.log_nonneg <| by norm_cast; linarith ) ] ; exact le_mul_of_one_le_right ( abs_nonneg _ ) <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ⟩;
    refine Asymptotics.IsBigO.trans ?_ ( h_const.add ( h_log_g.const_mul_left B ) );
    rw [Asymptotics.isBigO_iff]
    simp at *;
    exact ⟨ 1, 0, fun n hn ↦ by rw [ one_mul ] ; exact le_trans ( hAB n ) ( le_abs_self _ ) ⟩;
  exact log_iff_rlog.mpr h_trans

private lemma log_le_const_mul_log_add_const {f : ℕ → ℕ} (hf : f ∈ GrowthRate.log) :
    ∃ (C D : ℝ), ∀ n, (f n : ℝ) ≤ C * (Nat.log 2 n) + D := by
  unfold log bigO at hf;
  -- Since $f$ is $O(\log n)$, there exists $C$ and $N$ such that for all $n \geq N$, $f(n) \leq C \log n$.
  obtain ⟨C, N, hN⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * Nat.log 2 n := by
    norm_num [ Asymptotics.isBigO_iff ] at hf;
    rcases hf with ⟨ c, N, hc ⟩ ; exact ⟨ ⌈c⌉₊, N, fun n hn ↦ by exact_mod_cast hc n hn |> le_trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| Nat.cast_nonneg _ ⟩ ;
  -- Let $D = \max_{n < N} f(n)$.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n < N, f n ≤ D := by
    exact ⟨ Finset.sup ( Finset.range N ) f, fun n hn ↦ Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
  exact ⟨ C, D, fun n ↦ if hn : n < N then by exact le_trans ( Nat.cast_le.mpr ( hD n hn ) ) ( by norm_cast; nlinarith ) else by exact le_trans ( Nat.cast_le.mpr ( hN n ( le_of_not_gt hn ) ) ) ( by norm_cast; nlinarith ) ⟩

private lemma log_of_quasipoly_mem_polylog (hg : g ∈ quasipoly) : (fun n ↦ Nat.log 2 (g n)) ∈ polylog := by
  -- Since `g ∈ quasipoly`, we know that `g(n) = O(2^{(\log n)^C})` for some `C`.
  obtain ⟨C, hC⟩ : ∃ C : ℕ, (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ (2 : ℝ) ^ (Nat.log 2 n ^ C) : ℕ → ℝ) := by
    obtain ⟨ C, hC ⟩ := hg;
    use C;
    norm_num [ Asymptotics.isBigO_iff, Asymptotics.IsBigOWith ] at *;
    exact ⟨ hC.choose, hC.choose_spec.choose, fun n hn ↦ le_trans ( hC.choose_spec.choose_spec n hn ) ( by norm_num [ Norm.norm ] ) ⟩;
  -- Taking the logarithm, we get `log(g(n)) ≤ log(K * 2^{(\log n)^C}) ≈ log K + (\log n)^C`.
  have h_log_bound : ∃ C' D : ℝ, ∀ n, (Nat.log 2 (g n) : ℝ) ≤ C' * (Nat.log 2 n) ^ C + D := by
    -- Since `g(n) = O(2^{(\log n)^C})`, we have `g(n) ≤ K * 2^{(\log n)^C}` for some constant `K`.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n, g n ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
      -- By definition of big-O, there exists a constant K such that g(n) ≤ K * 2^(Nat.log 2 n ^ C) for all n.
      obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n, g n ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
        rw [ Asymptotics.isBigO_iff' ] at hC;
        norm_num +zetaDelta at *;
        obtain ⟨ c, hc₀, a, ha ⟩ := hC;
        -- Let $K = \max_{0 \leq n < a} g(n) / 2^{(\log n)^C}$.
        obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n < a, (g n : ℝ) ≤ K * 2 ^ (Nat.log 2 n ^ C) := by
          use ∑ n ∈ Finset.range a, (g n : ℝ) / 2 ^ (Nat.log 2 n ^ C);
          intro n hn; rw [ Finset.sum_mul _ _ _ ] ; exact le_trans ( by rw [ div_mul_cancel₀ _ ( by positivity ) ] ) ( Finset.single_le_sum ( fun x _ ↦ by positivity ) ( Finset.mem_range.mpr hn ) ) ;
        exact ⟨ Max.max K c, fun n ↦ if hn : n < a then le_trans ( hK n hn ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) else le_trans ( ha n ( le_of_not_gt hn ) ) ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) ) ⟩;
      exact ⟨ ⌈K⌉₊, fun n ↦ by exact_mod_cast le_trans ( hK n ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩;
    -- Taking the logarithm, we get `log(g(n)) ≤ log(K * 2^{(\log n)^C}) = log K + (\log n)^C`.
    have h_log_bound : ∀ n, (Nat.log 2 (g n) : ℝ) ≤ Real.log K / Real.log 2 + (Nat.log 2 n) ^ C := by
      intro n
      have h_log_bound : (Nat.log 2 (g n) : ℝ) ≤ Real.log (K * 2 ^ (Nat.log 2 n ^ C)) / Real.log 2 := by
        rw [ le_div_iff₀ ( Real.log_pos one_lt_two ), ← Real.log_pow ];
        by_cases hn : g n = 0;
        · norm_num [ hn ];
          rcases K with ( _ | K ) <;> norm_num at *;
          exact Real.log_nonneg ( one_le_mul_of_one_le_of_one_le ( by linarith ) ( one_le_pow₀ ( by norm_num ) ) );
        · exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self 2 hn |> le_trans <| mod_cast hK n );
      by_cases hK : K = 0 <;> simp_all [ Real.log_mul, Real.log_pow ];
      exact h_log_bound.trans_eq ( by rw [ add_div, mul_div_cancel_right₀ _ ( by positivity ) ] );
    exact ⟨ 1, Real.log K / Real.log 2, fun n ↦ by linarith [ h_log_bound n ] ⟩;
  -- This is bounded by a polynomial in `\log n`, so it is in `polylog`.
  obtain ⟨C', D, h_log_bound⟩ := h_log_bound;
  have h_polylog : (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n) ^ C : ℕ → ℝ) := by
    refine' Asymptotics.IsBigO.of_bound ( |C'| + |D| ) _;
    norm_num +zetaDelta at *;
    exact ⟨ 2, fun n hn ↦ le_trans ( h_log_bound n ) ( by cases abs_cases C' <;> cases abs_cases D <;> nlinarith [ show ( Nat.log 2 n : ℝ ) ^ C ≥ 1 by exact one_le_pow₀ ( mod_cast Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ) ] ) ⟩;
  use C
  rw [ Asymptotics.isBigO_iff ] at *;
  aesop

theorem log_comp_quasipoly (hf : f ∈ log) (hg : g ∈ quasipoly) : f ∘ g ∈ polylog := by
  have := log_of_quasipoly_mem_polylog hg;
  -- By definition of `polylog`, we know that `h(n) = O((\log n)^K)` for some `K`.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (fun n ↦ Nat.log 2 (g n) : ℕ → ℕ) ∈ bigO (fun n ↦ (Nat.log 2 n) ^ K) := by
    exact this;
  -- Since `f \in log`, by `log_le_const_mul_log_add_const`, `f(x) \le A \log x + B`.
  obtain ⟨A, B, hA⟩ : ∃ A B : ℝ, ∀ n, (f n : ℝ) ≤ A * (Nat.log 2 n) + B :=
    log_le_const_mul_log_add_const hf
  -- Since `h(n) = O((\log n)^K)`, `A h(n) + B` is also `O((\log n)^K)` (as `polylog` is closed under scalar multiplication and addition).
  have h_polylog : (fun n ↦ A * (Nat.log 2 (g n) : ℝ) + B) =O[.atTop] (fun n ↦ (Nat.log 2 n) ^ K : ℕ → ℝ) := by
    -- Since `h(n) = O((\log n)^K)`, multiplying by a constant `A` preserves the big-O.
    have h_mul_const : (fun n ↦ A * (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n) ^ K : ℕ → ℝ) := by
      have h_mul_const : (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n) ^ K : ℕ → ℝ) := by
        convert hK using 1;
        norm_num [ Asymptotics.isBigO_iff, GrowthRate.bigO ];
      exact h_mul_const.const_mul_left A;
    refine h_mul_const.add ?_ |> fun h ↦ h.trans ?_
    · rw [ Asymptotics.isBigO_iff ];
      use ‖B‖
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn
      norm_num
      exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ ( mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith)))
    · apply Asymptotics.isBigO_refl
  use K
  rw [Asymptotics.isBigO_iff] at *
  norm_num at *
  choose C D hC using h_polylog
  exact ⟨C, D, fun n hn ↦ (hA _).trans <| (le_abs_self _).trans (hC n hn)⟩

lemma Nat.log2_pow_le (b n : ℕ) : Nat.log 2 (b ^ n) ≤ n * (Nat.log 2 b + 1) := by
  -- By definition of logarithm, we know that $\log_2(b^n) = n \log_2(b)$.
  have h_log : Nat.log 2 (b ^ n) ≤ n * Nat.log 2 b + n := by
    have h_log_def : b ^ n ≤ 2 ^ (n * Nat.log 2 b + n) := by
      rw [ pow_add, pow_mul' ];
      rw [ ← mul_pow ];
      exact Nat.pow_le_pow_left ( by rw [ ← pow_succ ] ; exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ) _
    exact Nat.le_trans ( Nat.log_mono_right h_log_def ) ( by norm_num [ Nat.log_pow ] );
  linarith

private lemma exists_le_log_add_const {f : ℕ → ℕ} (hf : f ∈ GrowthRate.log) :
    ∃ C D, ∀ n, f n ≤ C * Nat.log 2 n + D := by
  -- By definition of bigO, there exists a constant C such that f(n) ≤ C * Nat.log 2 n for all n ≥ N.
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, f n ≤ C * Nat.log 2 n := by
    -- By definition of bigO, there exists a constant C such that for all n ≥ N, f(n) ≤ C * Nat.log 2 n. Use this fact.
    have h_bound : ∃ C, ∀ᶠ n in .atTop, f n ≤ C * Nat.log 2 n := by
      have := hf
      unfold GrowthRate.log at this;
      unfold GrowthRate.bigO at this;
      norm_num [ Asymptotics.isBigO_iff ] at this;
      obtain ⟨ C, a, hC ⟩ := this; exact ⟨ ⌈C⌉₊, Filter.eventually_atTop.mpr ⟨ a, fun n hn ↦ by rw [ ← @Nat.cast_le ℝ ] ; push_cast; nlinarith [ Nat.le_ceil C, hC n hn, show ( Nat.log 2 n : ℝ ) ≥ 0 by positivity ] ⟩ ⟩ ;
    aesop
  -- Let $D$ be the maximum of $f(n)$ for $n < N$.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n < N, f n ≤ D := by
    exact ⟨(Finset.range N).sup f, fun n hn ↦ Finset.le_sup (f := f) (Finset.mem_range.mpr hn)⟩
  exact ⟨C, D, fun n ↦ if hn : n < N then le_trans (hD n hn) ( Nat.le_add_left _ _ ) else le_trans ( hC n ( le_of_not_gt hn ) ) ( Nat.le_add_right _ _ ) ⟩

theorem log_comp_exp (hf : f ∈ log) (hg : g ∈ exp) : f ∘ g ∈ linear := by
  -- Since $g \in \text{exp}$, there exists a base $B$ such that $g(n) = O(B^n)$ which means eventually $g(n) \le K B^n$ for some constant $K$.
  obtain ⟨B, K, hB⟩ : ∃ B K, ∀ᶠ n in .atTop, g n ≤ K * B ^ n := by
    unfold GrowthRate.exp at hg;
    norm_num [ Asymptotics.isBigO_iff ] at hg;
    obtain ⟨ C, c, a, hc ⟩ := hg; use C, ⌈c⌉₊; filter_upwards [ Filter.eventually_ge_atTop a ] with n hn; exact_mod_cast hc n hn |> le_trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| by positivity;
  -- Using `Nat.log_mul_le`, $\log(K B^n) \le \log K + \log(B^n) + 1$.
  -- Using `Nat.log2_pow_le`, $\log(B^n) \le n (\log B + 1)$.
  have h_log_bound : ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 K + n * (Nat.log 2 B + 1) + 1 := by
    filter_upwards [ hB, Filter.eventually_gt_atTop 0 ] with n hn hn' ; rcases eq_or_ne K 0 with rfl | hK' <;> rcases eq_or_ne B 0 with rfl | hB' <;> simp_all [ Nat.log_of_lt ] ;
    refine' Nat.le_trans ( Nat.log_mono_right hn ) _;
    refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
    · positivity;
    · -- By properties of logarithms and exponents, we can simplify the right-hand side.
      have h_simp : K * B ^ n < 2 ^ (Nat.log 2 K + 1) * 2 ^ (n * (Nat.log 2 B + 1)) := by
        exact mul_lt_mul'' ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ( by rw [ pow_mul' ] ; exact Nat.pow_lt_pow_left ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ( by positivity ) ) ( by positivity ) ( by positivity );
      exact h_simp.trans_le ( by rw [ ← pow_add ] ; exact pow_le_pow_right₀ ( by decide ) ( by linarith ) );
  -- Using `GrowthRate.exists_le_log_add_const`, there exist constants $C_f, D_f$ such that $f(x) \le C_f \log x + D_f$ for all $x$.
  obtain ⟨C_f, D_f, hC_f⟩ : ∃ C_f D_f, ∀ x, f x ≤ C_f * Nat.log 2 x + D_f :=
    exists_le_log_add_const hf
  -- Combining these, $f(g(n)) \le C_f (\log K + n(\log B + 1) + 1) + D_f$, which is $O(n)$.
  have h_combined : ∀ᶠ n in .atTop, f (g n) ≤ C_f * (Nat.log 2 K + n * (Nat.log 2 B + 1) + 1) + D_f := by
    filter_upwards [ h_log_bound ] with n hn using le_trans ( hC_f _ ) ( by gcongr );
  -- This simplifies to $O(n)$, so $f \circ g \in \text{linear}$.
  have h_linear : ∃ C, ∀ᶠ n in .atTop, f (g n) ≤ C * n := by
    use C_f * (Nat.log 2 B + 1) + C_f * Nat.log 2 K + C_f + D_f + 1;
    filter_upwards [ h_combined, Filter.eventually_gt_atTop 0 ] with n hn hn' using by nlinarith [ show 0 ≤ C_f * Nat.log 2 K by positivity, show 0 ≤ C_f * Nat.log 2 B by positivity ] ;
  obtain ⟨ C, hC ⟩ := h_linear;
  refine' Asymptotics.IsBigO.of_bound ( C + 1 ) _;
  filter_upwards [ hC, Filter.eventually_gt_atTop 0 ] with n hn hn'
  norm_num
  exact_mod_cast hn.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem sublinear_comp_linear (hf : f ∈ sublinear) (hg : g ∈ linear) : f ∘ g ∈ sublinear := by
    -- Let's start by unfolding the definition of `f ∈ sublinear` and `g ∈ linear`.
  obtain ⟨c, hc⟩ : ∃ c > 0, ∀ᶠ x in .atTop, |(f x : ℝ)| ≤ c * x := by
    -- By definition of sublinear, we have that for any ε > 0, there exists an N such that for all n ≥ N, |f(n)| ≤ ε * n.
    have h_sublinear : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f n : ℝ)| ≤ ε * n := by
      intro ε hε_pos
      simp
      have := hf.def ( show 0 < ε by positivity )
      simp_all
    exact ⟨ 1, zero_lt_one, by obtain ⟨ N, hN ⟩ := h_sublinear 1 zero_lt_one; filter_upwards [ Filter.Ici_mem_atTop N ] with n hn; exact hN n hn ⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ x in .atTop, |(g x : ℝ)| ≤ C * x := by
    unfold GrowthRate.linear at hg;
    rw [ GrowthRate.bigO ] at hg;
    norm_num [ Asymptotics.isBigO_iff ] at hg;
    exact ⟨ hg.choose, Filter.eventually_atTop.mpr ⟨ hg.choose_spec.choose, fun x hx ↦ by simpa [ abs_of_nonneg ] using hg.choose_spec.choose_spec x hx ⟩ ⟩;
  -- Since `f ∈ sublinear`, for any `ε > 0`, there exists `N_f` such that for all `x ≥ N_f`, `f(x) ≤ ε * x`.
  have h_sublinear : ∀ ε > 0, ∃ N_f, ∀ x ≥ N_f, (f x : ℝ) ≤ ε * x := by
    intro ε hε;
    have := hf.congr' ( by aesop ) ( by aesop );
    have := this.def hε; aesop;
  -- Since `g ∈ linear`, there exists `C > 0` such that for all `x ≥ N_g`, `g(x) ≤ C * x`.
  obtain ⟨C, hC⟩ : ∃ C > 0, ∀ᶠ x in .atTop, |(g x : ℝ)| ≤ C * x := by
    exact ⟨ Max.max C 1, by positivity, hC.mono fun x hx ↦ le_trans hx <| mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| Nat.cast_nonneg _ ⟩;
  -- Let's choose any `ε > 0`.
  have h_eps : ∀ ε > 0, ∃ N, ∀ x ≥ N, (f (g x) : ℝ) ≤ ε * x := by
    intro ε hε_pos
    obtain ⟨N_f, hN_f⟩ : ∃ N_f, ∀ x ≥ N_f, (f x : ℝ) ≤ (ε / (C + 1)) * x := h_sublinear (ε / (C + 1)) (by
    exact div_pos hε_pos ( add_pos hC.1 zero_lt_one ))
    obtain ⟨N_g, hN_g⟩ : ∃ N_g, ∀ x ≥ N_g, |(g x : ℝ)| ≤ C * x := by
      exact Filter.eventually_atTop.mp hC.2
    obtain ⟨M, hM⟩ : ∃ M, ∀ x < N_f, (f x : ℝ) ≤ M := by
      exact ⟨ ∑ x ∈ Finset.range N_f, ( f x : ℝ ), fun x hx ↦ Finset.single_le_sum ( fun x _ ↦ Nat.cast_nonneg ( f x ) ) ( Finset.mem_range.mpr hx ) ⟩
    use max N_g (⌈M / ε⌉₊ + 1);
    intro x hx
    by_cases h_case : g x < N_f;
    · exact le_trans ( hM _ h_case ) ( by nlinarith [ Nat.le_ceil ( M / ε ), mul_div_cancel₀ M hε_pos.ne', show ( x : ℝ ) ≥ ⌈M / ε⌉₊ + 1 by exact_mod_cast le_trans ( le_max_right _ _ ) hx ] );
    · have := hN_f ( g x ) ( by linarith );
      rw [ div_mul_eq_mul_div, le_div_iff₀ ] at this <;> nlinarith [ abs_le.mp ( hN_g x ( le_trans ( le_max_left _ _ ) hx ) ), Nat.le_ceil ( M / ε ), mul_div_cancel₀ M hε_pos.ne' ];
  refine' Asymptotics.isLittleO_iff.2 fun ε hε ↦ _;
  obtain ⟨ N, hN ⟩ := h_eps ε hε; filter_upwards [ Filter.eventually_ge_atTop N ] with x hx using by simpa [ abs_of_nonneg, hε.le ] using hN x hx;

/-
If g is linear, then log(g(n)) is logarithmic.
-/
private lemma log_comp_linear {g : ℕ → ℕ} (hg : g ∈ GrowthRate.linear) : (fun n ↦ Nat.log 2 (g n)) ∈ GrowthRate.log := by
  -- Applying the definition of `linear`, we know that there exists a constant $C$ such that $g(n) \leq Cn$ for all $n$.
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ n in .atTop, g n ≤ C * n := by
    obtain ⟨ C, hC ⟩ := Asymptotics.isBigO_iff.mp hg;
    exact ⟨ ⌈C⌉₊, by filter_upwards [ hC, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂; exact_mod_cast ( by simpa using le_trans ( le_abs_self _ ) ( hx₁.trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| by positivity ) : ( g x : ℝ ) ≤ ↑⌈C⌉₊ * x ) ⟩;
  -- For sufficiently large $n$, $\log(g(n)) \le \log(Cn) = \log C + \log n$.
  have h_log_bound : ∃ D, ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 C + Nat.log 2 n + D := by
    refine' ⟨ 2, _ ⟩ ; filter_upwards [ hC ] with n hn ; rcases eq_or_ne ( g n ) 0 with hn' | hn' <;> simp_all [ Nat.log_of_lt ];
    refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
    · aesop;
    · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) C; ( have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) n; ( norm_num [ Nat.pow_succ', Nat.pow_add ] at *; nlinarith; ) );
  obtain ⟨ D, hD ⟩ := h_log_bound;
  refine' Asymptotics.IsBigO.of_bound ( Nat.log 2 C + D + 1 ) _;
  norm_num +zetaDelta at *;
  obtain ⟨ a, ha ⟩ := hD;
  exact ⟨ a + 2, fun n hn ↦ by norm_cast; nlinarith [ ha n ( by linarith ), Nat.log_pos one_lt_two ( by linarith : 1 < n ) ] ⟩

/-
If g is linear, then g(n) * log(g(n)) is linearithmic.
-/
private lemma linear_mul_log_comp_linear {g : ℕ → ℕ} (hg : g ∈ GrowthRate.linear) :
    (fun n ↦ g n * Nat.log 2 (g n)) ∈ GrowthRate.linearithmic := by
  -- Since $g \in \text{linear}$, $g(n) = O(n)$.
  have h_g_linear : g ∈ GrowthRate.linear := by
    assumption;
  -- By `GrowthRate.log_comp_linear`, $\log(g(n)) = O(\log n)$.
  have h_log_g_linear : (fun n ↦ Nat.log 2 (g n)) ∈ GrowthRate.log := by
    exact log_comp_linear hg;
  -- Thus $g(n) \log(g(n)) = O(n \log n)$.
  apply GrowthRate.linearithmic_of_linear_mul_log h_g_linear h_log_g_linear

theorem linearithmic_comp (hf : f ∈ linearithmic) (hg : g ∈ linear) : f ∘ g ∈ linearithmic := by
  unfold GrowthRate.linearithmic at *;
  -- Since $g \in \text{linear}$, there exists $C, N$ such that $g(n) \le Cn$ for $n \ge N$.
  obtain ⟨C, N, hC⟩ : ∃ C N, ∀ n ≥ N, g n ≤ C * n := by
    obtain ⟨ C, N, hC ⟩ := hg.exists_pos;
    rw [ Asymptotics.IsBigOWith ] at hC;
    norm_num +zetaDelta at *;
    exact ⟨ ⌈C⌉₊, hC.choose, fun n hn ↦ by exact_mod_cast le_trans ( hC.choose_spec n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩;
  -- Since $f \in \text{linearithmic}$, there exists $D, M$ such that $f(x) \le Dx \log x$ for $x \ge M$.
  obtain ⟨D, M, hD⟩ : ∃ D M, ∀ x ≥ M, f x ≤ D * x * Nat.log 2 x := by
    rw [ GrowthRate.bigO ] at hf;
    norm_num [ Asymptotics.isBigO_iff ] at hf;
    obtain ⟨ c, a, hc ⟩ := hf; use ⌈c⌉₊, a; intros x hx; specialize hc x hx; rw [ ← @Nat.cast_le ℝ ] ; push_cast; nlinarith [ Nat.le_ceil c, show ( x : ℝ ) * Nat.log 2 x ≥ 0 by positivity ] ;
  -- For any $n$, if $g(n) \ge M$, then $f(g(n)) \le D g(n) \log g(n)$.
  have hfg_bound : ∀ n ≥ N, f (g n) ≤ D * (C * n) * Nat.log 2 (C * n) + ∑ x ∈ Finset.range M, f x := by
    intro n hn;
    by_cases hmn : g n < M;
    · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Finset.single_le_sum ( fun x _ ↦ Nat.zero_le ( f x ) ) ( Finset.mem_range.mpr hmn ) );
    · exact le_add_of_le_of_nonneg ( le_trans ( hD _ ( le_of_not_gt hmn ) ) ( by gcongr <;> linarith [ hC n hn ] ) ) ( Nat.zero_le _ );
  -- Since $C$ is a constant, we can factor it out of the logarithm.
  have hfg_bound_simplified : ∀ n ≥ N, f (g n) ≤ D * C * n * (Nat.log 2 n + Nat.log 2 C + 1) + ∑ x ∈ Finset.range M, f x := by
    intros n hn
    specialize hfg_bound n hn
    have h_log_bound : Nat.log 2 (C * n) ≤ Nat.log 2 n + Nat.log 2 C + 1 := by
      by_cases hC : C = 0 <;> by_cases hn : n = 0 <;> simp_all
      refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
      · positivity;
      · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) n; ( have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) C; ( norm_num [ Nat.pow_succ', Nat.pow_add ] at *; nlinarith [ Nat.pos_of_ne_zero hC, Nat.pos_of_ne_zero hn ] ; ) );
    exact hfg_bound.trans ( by nlinarith [ show 0 ≤ D * C * n by positivity ] );
  -- We can bound the expression $D * C * n * (Nat.log 2 n + Nat.log 2 C + 1) + \sum x ∈ Finset.range M, f x$ by $O(n \log n)$.
  have hfg_bound_final : ∃ K, ∀ n ≥ N, f (g n) ≤ K * n * Nat.log 2 n + K := by
    use D * C * (Nat.log 2 C + 2) + ∑ x ∈ Finset.range M, f x + 1;
    intro n hn; specialize hfg_bound_simplified n hn; rcases k : Nat.log 2 n with ( _ | k ) <;> simp_all
    · interval_cases n <;> norm_num at * <;> nlinarith [ show 0 ≤ D * C by positivity ];
    · grind;
  obtain ⟨ K, hK ⟩ := hfg_bound_final;
  refine' Asymptotics.IsBigO.of_bound ( K + K ) _;
  norm_num +zetaDelta at *;
  exact ⟨ N + 2, fun n hn ↦ by norm_cast; nlinarith [ hK n ( by linarith ), show ( n : ℕ ) * Nat.log 2 n ≥ n by exact Nat.le_of_lt_succ <| by nlinarith [ Nat.le_log_of_pow_le ( by decide ) <| show 2 ^ 1 ≤ n by linarith ] ] ⟩

private lemma log_quasilinear_bound (D : ℕ) :
    (fun n ↦ (Nat.log 2 (n * (Nat.log 2 n)^D) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
  -- Using the lemma `Nat.log_mul_le_add`, we bound `log₂(n * log₂(n)^D)`.
  have h_log_mul_le_add : ∀ n ≥ 2, Nat.log 2 (n * Nat.log 2 n ^ D) ≤ Nat.log 2 n + D * (Nat.log 2 (Nat.log 2 n) + 1) + 1 := by
    intro n hn
    have h_log_mul_le_add : Nat.log 2 (n * Nat.log 2 n ^ D) ≤ Nat.log 2 n + Nat.log 2 (Nat.log 2 n ^ D) + 1 := by
      have h_log_mul_le_add : ∀ a b : ℕ, a ≥ 2 → b ≥ 2 → Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
        intro a b ha hb;
        refine Nat.le_of_lt_succ <| Nat.log_lt_of_lt_pow ?_ ?_ <;> norm_num;
        · aesop;
        · -- By definition of logarithm, we know that $a < 2^{Nat.log 2 a + 1}$ and $b < 2^{Nat.log 2 b + 1}$.
          have h_log_a : a < 2 ^ (Nat.log 2 a + 1) := by
            exact Nat.lt_pow_succ_log_self ( by decide ) _
          have h_log_b : b < 2 ^ (Nat.log 2 b + 1) := by
            exact Nat.lt_pow_succ_log_self ( by decide ) _;
          convert mul_lt_mul'' h_log_a h_log_b ( by positivity ) ( by positivity ) using 1 ; ring;
      by_cases h₂ : Nat.log 2 n ^ D ≥ 2;
      · exact h_log_mul_le_add _ _ hn h₂;
      · interval_cases _ : Nat.log 2 n ^ D <;> simp_all +decide;
    have h_log_pow_le : Nat.log 2 (Nat.log 2 n ^ D) ≤ D * (Nat.log 2 (Nat.log 2 n) + 1) := by
      have h_log_pow_le : ∀ a k : ℕ, a > 0 → Nat.log 2 (a ^ k) ≤ k * (Nat.log 2 a + 1) := by
        intros a k ha_pos
        have h_log_pow_le : a ^ k ≤ 2 ^ (k * (Nat.log 2 a + 1)) := by
          rw [ pow_mul' ] ; gcongr ; exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ );
        exact Nat.le_trans ( Nat.log_mono_right h_log_pow_le ) ( by rw [ Nat.log_pow ( by decide ) ] );
      exact h_log_pow_le _ _ ( Nat.log_pos one_lt_two hn );
    linarith;
  -- Since $Nat.log 2 (Nat.log 2 n) \le Nat.log 2 n$, we have $Nat.log 2 (n * Nat.log 2 n ^ D) \le Nat.log 2 n + D * (Nat.log 2 n + 1) + 1$.
  have h_log_mul_le_add' : ∀ n ≥ 2, Nat.log 2 (n * Nat.log 2 n ^ D) ≤ Nat.log 2 n + D * (Nat.log 2 n + 1) + 1 := by
    exact fun n hn ↦ le_trans ( h_log_mul_le_add n hn ) ( by gcongr ; exact Nat.log_le_self _ _ );
  norm_num [ Asymptotics.isBigO_iff ];
  refine' ⟨ D + D + 2, 2, fun n hn ↦ _ ⟩
  norm_cast
  nlinarith [ h_log_mul_le_add' n hn, Nat.le_log_of_pow_le ( by linarith ) ( show 2 ^ 1 ≤ n by linarith ) ]

theorem quasilinear_comp (hf : f ∈ quasilinear) (hg : g ∈ quasilinear) : f ∘ g ∈ quasilinear := by
  -- Let's unfold the definition of `quasilinear`.
  obtain ⟨C₁, hC₁⟩ := hf
  obtain ⟨C₂, hC₂⟩ := hg;
  -- Let $M$ be such that $g(n) \le M * n * (\log n)^D$ for large $n$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ n in .atTop, g n ≤ M * n * (Nat.log 2 n)^C₂ := by
    rw [ Asymptotics.isBigO_iff' ] at hC₂;
    norm_num +zetaDelta at *;
    obtain ⟨ c, hc₀, a, ha ⟩ := hC₂; exact ⟨ ⌈c⌉₊, a, fun n hn ↦ by rw [ ← @Nat.cast_le ℝ ] ; push_cast; nlinarith [ Nat.le_ceil c, ha n hn, show ( 0 : ℝ ) ≤ n * Nat.log 2 n ^ C₂ by positivity ] ⟩ ;
  -- Using `log_quasilinear_bound`, $\log(g(n)) = O(\log n)$.
  have h_log_g_growth : (fun n ↦ (Nat.log 2 (g n) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
    -- We'll use that $g(n) \le M * n * (\log n)^D$ to bound $\log(g(n))$.
    have h_log_g_bound : ∀ᶠ n in .atTop, Nat.log 2 (g n) ≤ Nat.log 2 (M * n * (Nat.log 2 n)^C₂) := by
      filter_upwards [ hM ] with n hn using Nat.log_mono_right hn;
    -- Using `log_quasilinear_bound`, $\log(M * n * (\log n)^D) = O(\log n)$.
    have h_log_Mn_logD_growth : (fun n ↦ (Nat.log 2 (M * n * (Nat.log 2 n)^C₂) : ℤ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℤ)) := by
      have := log_quasilinear_bound C₂;
      rcases M with ( _ | M ) <;> simp_all [ mul_assoc ];
      · exact Asymptotics.isBigO_zero _ _;
      · -- Using the properties of logarithms, we can bound $\log((M + 1) * (n * (\log n)^C₂))$.
        have h_log_bound : ∀ᶠ n in .atTop, Nat.log 2 ((M + 1) * (n * (Nat.log 2 n)^C₂)) ≤ Nat.log 2 (n * (Nat.log 2 n)^C₂) + Nat.log 2 (M + 1) + 1 := by
          refine' Filter.eventually_atTop.mpr ⟨ 2, fun n hn ↦ _ ⟩;
          refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
          · exact mul_ne_zero ( Nat.succ_ne_zero _ ) ( mul_ne_zero ( by linarith ) ( pow_ne_zero _ ( Nat.ne_of_gt ( Nat.log_pos one_lt_two hn ) ) ) );
          · rw [ Nat.pow_succ ];
            rw [ pow_add, pow_add ];
            have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( n * Nat.log 2 n ^ C₂ );
            have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( M + 1 );
            norm_num [ Nat.pow_succ' ] at * ; nlinarith [ Nat.zero_le ( n * Nat.log 2 n ^ C₂ ) ];
        rw [ Asymptotics.isBigO_iff ] at *;
        obtain ⟨ c, hc ⟩ := this;
        use c + Nat.log 2 (M + 1) + 1;
        filter_upwards [ h_log_bound, hc, Filter.eventually_gt_atTop 1 ] with n hn₁ hn₂ hn₃ ; norm_num at *;
        nlinarith [ show ( Nat.log 2 ( ( M + 1 ) * ( n * Nat.log 2 n ^ C₂ ) ) : ℝ ) ≤ Nat.log 2 ( n * Nat.log 2 n ^ C₂ ) + Nat.log 2 ( M + 1 ) + 1 by exact_mod_cast hn₁, show ( Nat.log 2 n : ℝ ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ];
    refine' Asymptotics.IsBigO.trans _ h_log_Mn_logD_growth;
    rw [ Asymptotics.isBigO_iff ];
    exact ⟨ 1, by filter_upwards [ h_log_g_bound ] with n hn; simpa using mod_cast hn ⟩;
  -- Now, $f(x) \le K (x (\log x)^C) + K'$ (handling small $g(n)$).
  have h_f_bound : ∃ K K', ∀ᶠ n in .atTop, f (g n) ≤ K * (g n * (Nat.log 2 (g n))^C₁) + K' := by
    rw [ Asymptotics.isBigO_iff' ] at *;
    obtain ⟨ K, hK₁, hK₂ ⟩ := hC₁;
    norm_num +zetaDelta at *;
    obtain ⟨ a, ha ⟩ := hK₂;
    -- Let $K'$ be such that $f(x) \le K * (x * (\log x)^C) + K'$ for all $x$.
    obtain ⟨ K', hK' ⟩ : ∃ K', ∀ x, f x ≤ K * (x * (Nat.log 2 x)^C₁) + K' := by
      exact ⟨ ∑ x ∈ Finset.range a, ( f x : ℝ ), fun x ↦ if hx : x < a then by exact le_add_of_nonneg_of_le ( by positivity ) ( Finset.single_le_sum ( fun x _ ↦ Nat.cast_nonneg ( f x ) ) ( Finset.mem_range.mpr hx ) ) else by exact le_add_of_le_of_nonneg ( ha x ( le_of_not_gt hx ) ) ( by positivity ) ⟩;
    exact ⟨ ⌈K⌉₊, ⌈K'⌉₊, a, fun n hn ↦ by have := hK' ( g n ) ; exact_mod_cast this.trans ( add_le_add ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| by positivity ) <| Nat.le_ceil _ ) ⟩;
  -- Substituting the bounds:
  obtain ⟨K, K', hK⟩ := h_f_bound
  have h_subst : ∃ K'', ∀ᶠ n in .atTop, f (g n) ≤ K'' * (n * (Nat.log 2 n)^(C₁ + C₂)) + K' := by
    -- Using `h_log_g_growth`, we can bound $(Nat.log 2 (g n))^C₁$ by $O((Nat.log 2 n)^C₁)$.
    obtain ⟨L, hL⟩ : ∃ L, ∀ᶠ n in .atTop, (Nat.log 2 (g n))^C₁ ≤ L * (Nat.log 2 n)^C₁ := by
      rw [ Asymptotics.isBigO_iff' ] at h_log_g_growth;
      norm_num +zetaDelta at *;
      obtain ⟨ c, hc₀, a, ha ⟩ := h_log_g_growth;
      exact ⟨ ⌈c ^ C₁⌉₊, a, fun n hn ↦ by rw [ ← @Nat.cast_le ℝ ] ; push_cast; exact le_trans ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( ha n hn ) _ ) ( by rw [ mul_pow ] ; exact mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩;
    -- Substitute the bounds from `hM` and `hL` into the inequality from `hK`.
    have h_subst : ∀ᶠ n in .atTop, f (g n) ≤ K * (M * n * (Nat.log 2 n)^C₂ * (L * (Nat.log 2 n)^C₁)) + K' := by
      filter_upwards [ hK, hM, hL ] with n hn hn' hn'' using le_trans hn <| by gcongr;
    exact ⟨ K * M * L, by filter_upwards [ h_subst ] with n hn; convert hn using 1; ring ⟩;
  obtain ⟨ K'', hK'' ⟩ := h_subst;
  refine' ⟨ C₁ + C₂, _ ⟩;
  rw [ Asymptotics.isBigO_iff ];
  norm_num at *;
  obtain ⟨ a, ha ⟩ := hK'';
  use K'' + K' + 1;
  exact ⟨ a + 2, fun n hn ↦ by norm_cast; nlinarith [ ha n ( by linarith ), show 0 < n * Nat.log 2 n ^ ( C₁ + C₂ ) from mul_pos ( by linarith ) ( pow_pos ( Nat.log_pos one_lt_two ( by linarith ) ) _ ) ] ⟩

private lemma exists_bound_of_isBigO {f h : ℕ → ℕ} (hf : (f · : ℕ → ℤ) =O[.atTop] (h · : ℕ → ℤ)) :
    ∃ C : ℕ, ∀ n, f n ≤ C * h n + C := by
  -- Since $f(n) = O(h(n))$, there exist constants $c, N$ such that for all $n \ge N$, $|f(n)| \le c |h(n)|$.
  obtain ⟨c, N, hc⟩ : ∃ c N, ∀ n ≥ N, f n ≤ c * h n := by
    rw [ Asymptotics.isBigO_iff' ] at hf;
    norm_num +zetaDelta at *;
    obtain ⟨ c, hc, N, hN ⟩ := hf; exact ⟨ ⌈c⌉₊, N, fun n hn ↦ by exact_mod_cast le_trans ( hN n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩ ;
  -- Let $M = \max_{n < N} f(n)$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ n < N, f n ≤ M := by
    exact ⟨ Finset.sup ( Finset.range N ) f, fun n hn ↦ Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
  exact ⟨ Max.max c M, fun n ↦ if hn : n < N then by nlinarith [ hM n hn, le_max_left c M, le_max_right c M ] else by nlinarith [ hc n ( le_of_not_gt hn ), le_max_left c M, le_max_right c M ] ⟩

theorem poly_comp_log (hf : f ∈ poly) (hg : g ∈ log) : f ∘ g ∈ polylog := by
  -- From `hf`, we have $f(n) = O(n^C)$ for some $C$. Using `exists_bound_of_isBigO`, there exists $A$ such that $f(n) \le A n^C + A$ for all $n$.
  obtain ⟨C, hc⟩ : ∃ C : ℕ, (f · : ℕ → ℤ) =O[.atTop] (· ^ C : ℕ → ℤ) := by
    exact hf
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ n, f n ≤ A * n ^ C + A := by
    rw [ Asymptotics.isBigO_iff' ] at hc;
    norm_num +zetaDelta at *;
    obtain ⟨ c, hc₀, a, ha ⟩ := hc;
    -- Let $A$ be a constant such that $f(n) \leq A \cdot n^C + A$ for all $n \geq a$.
    obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ n ≥ a, f n ≤ A * n ^ C + A := by
      exact ⟨ ⌈c⌉₊, fun n hn ↦ by have := ha n hn; exact_mod_cast ( by nlinarith [ Nat.le_ceil c, show ( n : ℝ ) ^ C ≥ 0 by positivity ] : ( f n : ℝ ) ≤ ⌈c⌉₊ * n ^ C + ⌈c⌉₊ ) ⟩;
    -- Let $A'$ be a constant such that $f(n) \leq A' \cdot n^C + A'$ for all $n < a$.
    obtain ⟨A', hA'⟩ : ∃ A' : ℕ, ∀ n < a, f n ≤ A' * n ^ C + A' := by
      exact ⟨ ∑ n ∈ Finset.range a, f n + 1, fun n hn ↦ by nlinarith [ Finset.single_le_sum ( fun n _ ↦ Nat.zero_le ( f n ) ) ( Finset.mem_range.mpr hn ), pow_nonneg ( Nat.zero_le n ) C ] ⟩;
    exact ⟨ Max.max A A', fun n ↦ if hn : n < a then le_trans ( hA' n hn ) ( by nlinarith [ Nat.le_max_right A A', pow_nonneg ( Nat.zero_le n ) C ] ) else le_trans ( hA n ( le_of_not_gt hn ) ) ( by nlinarith [ Nat.le_max_left A A', pow_nonneg ( Nat.zero_le n ) C ] ) ⟩;
  -- From `hg`, we have $g(n) = O(\log n)$. Using `exists_bound_of_isBigO`, there exists $B$ such that $g(n) \le B \log n + B$ for all $n$.
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ n, g n ≤ B * Nat.log 2 n + B :=
    exists_bound_of_isBigO hg
  -- Then $f(g(n)) \le A (g(n))^C + A \le A (B \log n + B)^C + A$.
  have hfg : ∀ n, f (g n) ≤ A * (B * Nat.log 2 n + B) ^ C + A := by
    exact fun n ↦ le_trans ( hA _ ) ( by gcongr ; exact hB _ );
  -- The term $(B \log n + B)^C$ is a polynomial in $\log n$ of degree $C$, so it is $O((\log n)^C)$.
  have h_polylog : ∃ D : ℕ, ∀ n, (B * Nat.log 2 n + B) ^ C ≤ D * (Nat.log 2 n) ^ C + D := by
    -- We can bound $(B * \log n + B)^C$ by $(2B * \log n)^C$ for large enough $n$.
    have h_bound : ∀ n, (B * Nat.log 2 n + B) ^ C ≤ (2 * B * Nat.log 2 n) ^ C + (2 * B) ^ C := by
      intro n; rcases eq_or_ne B 0 with rfl | hB₀ <;> simp_all [ two_mul ]
      rcases k : Nat.log 2 n with ( _ | k ) <;> simp_all [ add_mul ]
      · cases C <;> norm_num ; gcongr ; linarith;
      · exact le_add_of_le_of_nonneg ( Nat.pow_le_pow_left ( by nlinarith ) _ ) ( Nat.zero_le _ );
    use (2 * B) ^ C;
    exact fun n ↦ le_trans ( h_bound n ) ( by rw [ mul_pow ] );
  obtain ⟨ D, hD ⟩ := h_polylog;
  -- Therefore, $f(g(n)) \le A * D * (\log n)^C + A * D + A$, which is $O((\log n)^C)$.
  have h_final : ∃ E : ℕ, ∀ n, f (g n) ≤ E * (Nat.log 2 n) ^ C + E := by
    exact ⟨ A * D + A, fun n ↦ by nlinarith [ hfg n, hD n, pow_nonneg ( Nat.zero_le ( Nat.log 2 n ) ) C ] ⟩;
  obtain ⟨ E, hE ⟩ := h_final;
  use C
  apply Asymptotics.IsBigO.of_bound (E + E)
  simp +zetaDelta at *
  use 2
  intro n hn
  norm_cast
  nlinarith [hE n, Nat.one_le_pow C _ (Nat.log_pos one_lt_two hn)]

private lemma exists_poly_bound_nat {f : ℕ → ℕ} (hf : f ∈ GrowthRate.poly) : ∃ C K : ℕ, ∀ n, f n ≤ K * (n + 1) ^ C := by
  obtain ⟨C, hC⟩ : ∃ C : ℕ, (f · : ℕ → ℤ) =O[.atTop] (· ^ C : ℕ → ℤ) := by
    exact hf;
  rw [ Asymptotics.isBigO_iff' ] at hC;
  simp +zetaDelta at *;
  obtain ⟨c, hc_pos, N, hN⟩ := hC;
  have h_bound : ∃ K : ℕ, ∀ n ≥ N, f n ≤ K * (n + 1) ^ C := by
    use Nat.ceil c + 1;
    intro n hn
    specialize hN n hn
    exact_mod_cast ( by nlinarith [ Nat.le_ceil c, show ( n : ℝ ) ^ C ≤ ( n + 1 ) ^ C by gcongr ; linarith, show ( n + 1 : ℝ ) ^ C ≥ 0 by positivity ] : ( f n : ℝ ) ≤ ( ⌈c⌉₊ + 1 ) * ( n + 1 ) ^ C )
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n < N, f n ≤ K * (n + 1) ^ C := by
    exact ⟨ Finset.sup ( Finset.range N ) fun n ↦ f n, fun n hn ↦ by nlinarith [ Finset.le_sup ( f := fun n ↦ f n ) ( Finset.mem_range.mpr hn ), pow_pos ( Nat.succ_pos n ) C ] ⟩;
  exact ⟨ C, Max.max K h_bound.choose, fun n ↦ if hn : n < N then le_trans ( hK n hn ) ( Nat.mul_le_mul_right _ ( le_max_left _ _ ) ) else le_trans ( h_bound.choose_spec n ( le_of_not_gt hn ) ) ( Nat.mul_le_mul_right _ ( le_max_right _ _ ) ) ⟩

theorem poly_comp (hf : f ∈ poly) (hg : g ∈ poly) : f ∘ g ∈ poly := by
  obtain ⟨C_f, K_f, hf⟩ := exists_poly_bound_nat hf
  obtain ⟨C_g, K_g, hg⟩ := exists_poly_bound_nat hg;
  -- Then for all $n$, $f(g(n)) \le K_f (g(n)+1)^{C_f} \le K_f (K_g (n+1)^{C_g} + 1)^{C_f}$.
  have hfg_bound : ∀ n, f (g n) ≤ K_f * (K_g * (n + 1) ^ C_g + 1) ^ C_f := by
    exact fun n ↦ le_trans ( hf _ ) ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left ( by linarith [ hg n ] ) _ ) );
  -- We claim this is $O(n^{C_f * C_g})$.
  have hfg_poly : ∃ C K : ℕ, ∀ n, f (g n) ≤ K * (n + 1) ^ (C_f * C_g) := by
    -- We can bound $(K_g * (n + 1) ^ C_g + 1) ^ C_f$ by $(K_g + 1) ^ C_f * (n + 1) ^ (C_f * C_g)$.
    have hfg_bound_poly : ∀ n, (K_g * (n + 1) ^ C_g + 1) ^ C_f ≤ (K_g + 1) ^ C_f * (n + 1) ^ (C_f * C_g) := by
      intro n; rw [ pow_mul' ] ; rw [ ← mul_pow ] ; exact Nat.pow_le_pow_left ( by nlinarith [ pow_pos ( Nat.succ_pos n ) C_g ] ) _;
    exact ⟨ C_f * C_g, K_f * ( K_g + 1 ) ^ C_f, fun n ↦ le_trans ( hfg_bound n ) ( by nlinarith [ hfg_bound_poly n ] ) ⟩;
  obtain ⟨ C, K, hfg_poly ⟩ := hfg_poly; exact ⟨ C_f * C_g, by
    rw [ Asymptotics.isBigO_iff ];
    use K * 2 ^ (C_f * C_g);
    norm_num;
    refine' ⟨ 1, fun n hn ↦ le_trans ( Nat.cast_le.mpr ( hfg_poly n ) ) _ ⟩ ; norm_cast ; ring_nf;
    rw [ mul_assoc, ← mul_pow ] ; gcongr ; linarith ⟩ ;

private lemma isBigO_poly_comp_exp {k C : ℕ}
    (hf : (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(n ^ k) : ℕ → ℤ))
    (hg : (g · : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(C ^ n) : ℕ → ℤ)) :
    ∃ K : ℕ, (fun n ↦ f (g n) : ℕ → ℤ) =O[.atTop] (fun n ↦ ↑(K ^ n) : ℕ → ℤ) := by
  -- Let $M_f = \max_{x < N_f} f(x)$.
  obtain ⟨N_f, c_f, hM_f⟩ : ∃ N_f c_f, ∀ x, x ≥ N_f → f x ≤ c_f * x ^ k := by
    simp_all [ Asymptotics.isBigO_iff' ];
    obtain ⟨ c, hc, a, ha ⟩ := hf; exact ⟨ a, ⌈c⌉₊, fun x hx ↦ by have := ha x hx; exact_mod_cast this.trans ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩ ;
  -- Let $M_f = \max_{x < N_f} f(x)$. Then for all $x$, $f(x) \le M_f + c_f x^k$.
  obtain ⟨M_f, hM_f⟩ : ∃ M_f, ∀ x, f x ≤ M_f + c_f * x ^ k := by
    exact ⟨ Finset.sup ( Finset.range N_f ) f, fun x ↦ if hx : x < N_f then le_add_of_le_of_nonneg ( Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hx ) ) ( Nat.zero_le _ ) else le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( hM_f x ( le_of_not_gt hx ) ) ⟩;
  -- From $hg$, there exists $c_g > 0$ and $N_g$ such that for all $n \ge N_g$, $g(n) \le c_g C^n$.
  obtain ⟨c_g, N_g, hM_g⟩ : ∃ c_g N_g, ∀ n ≥ N_g, g n ≤ c_g * C ^ n := by
    rw [ Asymptotics.isBigO_iff' ] at hg;
    norm_num at *;
    obtain ⟨ c, hc₀, N_g, hN_g ⟩ := hg; exact ⟨ ⌈c⌉₊, N_g, fun n hn ↦ by exact_mod_cast le_trans ( hN_g n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩ ;
  -- So for $n \ge N_g$, $(g(n))^k \le (c_g C^n)^k = c_g^k (C^k)^n$.
  have h_bound : ∀ n ≥ N_g, (g n) ^ k ≤ c_g ^ k * (C ^ k) ^ n := by
    intro n hn; convert Nat.pow_le_pow_left ( hM_g n hn ) k using 1 ; ring;
  -- Let $K = \max(2, C^k)$. We claim $f(g(n)) = O(K^n)$.
  use max 2 (C ^ k)
  -- Thus $f(g(n)) \le M_f + c_f c_g^k (C^k)^n$.
  have h_final_bound : ∀ n ≥ N_g, f (g n) ≤ M_f + c_f * c_g ^ k * (C ^ k) ^ n := by
    exact fun n hn ↦ le_trans ( hM_f _ ) ( by nlinarith [ h_bound n hn ] );
  -- Since $K \ge C^k$ and $K \ge 2$, we have $(C^k)^n \le K^n$ and $1 \le K^n$.
  have h_K_bound : ∀ n ≥ N_g, (C ^ k) ^ n ≤ (max 2 (C ^ k)) ^ n ∧ 1 ≤ (max 2 (C ^ k)) ^ n := by
    exact fun n hn ↦ ⟨ Nat.pow_le_pow_left ( le_max_right _ _ ) _, Nat.one_le_pow _ _ ( by positivity ) ⟩;
  rw [ Asymptotics.isBigO_iff ];
  norm_num +zetaDelta at *;
  exact ⟨ M_f + c_f * c_g ^ k, N_g, fun n hn ↦ by erw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_trans ( Nat.cast_le.mpr ( h_final_bound n hn ) ) ( by norm_cast; nlinarith [ h_K_bound n hn, show 0 ≤ c_f * c_g ^ k by positivity ] ) ⟩

theorem poly_comp_exp (hf : f ∈ poly) (hg : g ∈ exp) : f ∘ g ∈ exp := by
  obtain ⟨k₁, hk₁⟩ := hf.imp fun _ ↦ mod_cast id
  obtain ⟨k₂, hk₂⟩ := hg.imp fun _ ↦ mod_cast id
  simpa [exp] using isBigO_poly_comp_exp hk₁ hk₂

private lemma log_bound_of_quasipoly {g : ℕ → ℕ} (hg : g ∈ GrowthRate.quasipoly) :
    ∃ D : ℕ, (fun n ↦ (Nat.log 2 (g n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ D) := by
  have := @log_comp_quasipoly;
  contrapose! this;
  refine' ⟨ fun n ↦ Nat.log 2 n, g, _, hg, _ ⟩;
  · refine' Asymptotics.isBigO_iff.mpr _;
    exact ⟨ 1, Filter.Eventually.of_forall fun n ↦ by norm_num ⟩;
  · intro H;
    obtain ⟨ C, hC ⟩ := H;
    refine' this C _;
    rw [ Asymptotics.isBigO_iff' ] at *;
    aesop

private lemma quasipoly_of_log_bound {f : ℕ → ℕ} (D : ℕ)
    (hf : (fun n ↦ (Nat.log 2 (f n) : ℝ)) =O[.atTop] (fun n ↦ (Nat.log 2 n : ℝ) ^ D)) :
    f ∈ GrowthRate.quasipoly := by
  -- From `hf`, we have `Nat.log 2 (f n) ≤ C * (Nat.log 2 n)^D` for large `n`. Then `f n ≤ 2^(Nat.log 2 (f n) + 1) ≤ 2^(C * (Nat.log 2 n)^D + 1)`.
  obtain ⟨C, hC⟩ : ∃ C : ℕ, ∀ᶠ n in Filter.atTop, Nat.log 2 (f n) ≤ C * (Nat.log 2 n) ^ D := by
    rw [ Asymptotics.isBigO_iff' ] at hf;
    norm_num +zetaDelta at *;
    obtain ⟨ c, hc, a, ha ⟩ := hf; exact ⟨ ⌈c⌉₊, a, fun n hn ↦ by exact_mod_cast Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil c, ha n hn, pow_nonneg ( Nat.cast_nonneg ( Nat.log 2 n ) : ( 0 :ℝ ) ≤ Nat.log 2 n ) D ] ⟩ ;
  -- We want to show `f n = O(2^((Nat.log 2 n)^K))`. Choose `K > D`. Then `(Nat.log 2 n)^K` eventually dominates `C * (Nat.log 2 n)^D + 1`.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K > D ∧ ∀ᶠ n in Filter.atTop, C * (Nat.log 2 n) ^ D + 1 ≤ (Nat.log 2 n) ^ K := by
    refine' ⟨ D + 1, _, _ ⟩ <;> norm_num;
    refine' ⟨ 2 ^ ( C + 1 ), fun n hn ↦ _ ⟩ ; rw [ pow_succ' ];
    nlinarith [ show C < Nat.log 2 n from Nat.le_log_of_pow_le ( by norm_num ) hn, show Nat.log 2 n ^ D > 0 from pow_pos ( Nat.log_pos ( by norm_num ) ( by linarith [ Nat.pow_le_pow_right ( by norm_num : 1 ≤ 2 ) ( show C + 1 ≥ 1 from Nat.le_add_left _ _ ) ] ) ) _ ];
  -- Then `f n ≤ 2^(Nat.log 2 (f n) + 1) ≤ 2^(C * (Nat.log 2 n)^D + 1) ≤ 2^((Nat.log 2 n)^K)`.
  have h_bound : ∀ᶠ n in Filter.atTop, f n ≤ 2 ^ ((Nat.log 2 n) ^ K) := by
    filter_upwards [ hC, hK.2 ] with n hn hn' using Nat.le_of_lt <| Nat.lt_pow_of_log_lt ( by norm_num ) <| by linarith;
  refine' ⟨ K, _ ⟩;
  rw [ Asymptotics.isBigO_iff' ];
  norm_num +zetaDelta at *;
  exact ⟨ 1, by norm_num, h_bound.choose, fun n hn ↦ by norm_num [ Norm.norm ] ; exact_mod_cast h_bound.choose_spec n hn ⟩

theorem quasipoly_comp (hf : f ∈ quasipoly) (hg : g ∈ quasipoly) : f ∘ g ∈ quasipoly := by
  -- Using the bounds from the lemma, obtain constants $Df$ and $Dg$.
  obtain ⟨Df, hDf⟩ := GrowthRate.log_bound_of_quasipoly hf
  obtain ⟨Dg, hDg⟩ := GrowthRate.log_bound_of_quasipoly hg;
  -- From (1), there exists `M` and `C` such that for `m \ge M`, `Nat.log 2 (f m) \le C * (Nat.log 2 m)^Df`.
  obtain ⟨M, C, hM⟩ : ∃ M C : ℕ, ∀ m ≥ M, (Nat.log 2 (f m) : ℝ) ≤ C * (Nat.log 2 m : ℝ) ^ Df := by
    rw [ Asymptotics.isBigO_iff' ] at hDf;
    obtain ⟨ c, hc₀, hc ⟩ := hDf; obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp hc; use M, ⌈c⌉₊; intros m hm; specialize hM m hm; norm_num at * ; exact le_trans hM <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| by positivity;
  -- For any `n`, consider `g n`.
  -- Case A: `g n < M`. Then `f (g n)` takes values in a finite set `{f 0, ..., f (M-1)}`. Thus `Nat.log 2 (f (g n))` is bounded by a constant.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n, (Nat.log 2 (f (g n)) : ℝ) ≤ K ∨ (Nat.log 2 (f (g n)) : ℝ) ≤ C * (Nat.log 2 (g n) : ℝ) ^ Df := by
    use Finset.sup (Finset.image (fun m ↦ Nat.log 2 (f m)) (Finset.range M)) id;
    exact fun n ↦ if hn : g n < M then Or.inl <| mod_cast Finset.le_sup ( f := id ) <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr hn else Or.inr <| hM _ <| le_of_not_gt hn;
  -- From (2), `Nat.log 2 (g n) \le C' * (Nat.log 2 n)^Dg` for large `n`.
  obtain ⟨C', hC'⟩ : ∃ C' : ℕ, ∀ᶠ n in .atTop, (Nat.log 2 (g n) : ℝ) ≤ C' * (Nat.log 2 n : ℝ) ^ Dg := by
    rw [ Asymptotics.isBigO_iff ] at hDg;
    norm_num +zetaDelta at *;
    obtain ⟨ c, a, hc ⟩ := hDg; exact ⟨ ⌈c⌉₊, a, fun n hn ↦ le_trans ( hc n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( by positivity ) ) ⟩ ;
  -- Substituting this into the bound from Case B gives `Nat.log 2 (f (g n)) \le C * (C' * (Nat.log 2 n)^Dg)^Df = C'' * (Nat.log 2 n)^(Dg*Df)`.
  have h_subst : ∃ C'' : ℕ, ∀ᶠ n in .atTop, (Nat.log 2 (f (g n)) : ℝ) ≤ C'' * (Nat.log 2 n : ℝ) ^ (Dg * Df) := by
    use K + C * C' ^ Df;
    filter_upwards [ hC', Filter.eventually_gt_atTop 1 ] with n hn hn';
    cases hK n <;> simp_all [ pow_mul ];
    · refine' le_trans ( Nat.cast_le.mpr ‹_› ) _;
      exact le_trans ( le_add_of_nonneg_right <| by positivity ) ( le_mul_of_one_le_right ( by positivity ) <| one_le_pow₀ <| one_le_pow₀ <| mod_cast Nat.le_log_of_pow_le ( by norm_num ) <| by linarith );
    · refine le_trans ‹_› ?_;
      refine le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) hn _ ) ( Nat.cast_nonneg _ ) ) ?_;
      ring_nf;
      exact le_add_of_nonneg_right ( by positivity );
  obtain ⟨ C'', hC'' ⟩ := h_subst;
  apply GrowthRate.quasipoly_of_log_bound;
  rw [ Asymptotics.isBigO_iff ];
  exact ⟨ C'', by filter_upwards [ hC'' ] with n hn; simpa using hn ⟩

/-
If g is O(log n) and C > 1, then C^(g n) is polynomially bounded.
-/
private lemma exists_pow_bound_of_exp_comp_log_real {g : ℕ → ℕ} {C : ℝ} (hC : 1 < C)
    (hg : (fun n ↦ (g n : ℝ)) =O[.atTop] (fun n ↦ Real.log (n : ℝ))) :
    ∃ K : ℝ, (fun n ↦ C ^ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ K) := by
  -- Since $g(n) = O(\log n)$, there exists $M$ such that $g(n) \le M \log n$ for large $n$.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ᶠ n in Filter.atTop, (g n : ℝ) ≤ M * Real.log n := by
    rw [ Asymptotics.isBigO_iff' ] at hg;
    obtain ⟨ M, hM₁, hM₂ ⟩ := hg; use M; filter_upwards [ hM₂, Filter.eventually_gt_atTop 1 ] with n hn hn'; rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ), Real.norm_of_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| pos_of_gt hn' ) ] at hn; exact hn;
  -- Therefore, $C^{g(n)} \le C^{M \log n} = n^{M \log C}$.
  have h_bound : ∀ᶠ n in Filter.atTop, (C : ℝ) ^ (g n : ℝ) ≤ (n : ℝ) ^ (M * Real.log C) := by
    filter_upwards [ hM, Filter.eventually_gt_atTop 1 ] with n hn hn';
    rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ];
    exact Real.exp_le_exp.mpr ( by nlinarith [ Real.log_pos hC ] );
  refine' ⟨ M * Real.log C, _ ⟩;
  rw [ Asymptotics.isBigO_iff ];
  exact ⟨ 1, by filter_upwards [ h_bound ] with n hn; rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; simpa using hn ⟩

/-
If f(n) is O(C^n) with C >= 1, then f(g(n)) is O(C^(g(n))).
-/
private lemma isBigO_comp_exp_of_isBigO_exp {f g : ℕ → ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hf : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))) :
    (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (fun n ↦ C ^ (g n : ℝ)) := by
  simp_all [ Asymptotics.isBigO_iff ];
  obtain ⟨ c, a, hc ⟩ := hf;
  -- Let $M$ be the maximum of $f(n)$ for $n < a$.
  obtain ⟨ M, hM ⟩ : ∃ M, ∀ n < a, f n ≤ M := by
    exact ⟨ Finset.sup ( Finset.range a ) f, fun n hn ↦ Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
  exact ⟨ Max.max c M, a, fun n hn ↦ if h : g n < a then by exact le_trans ( Nat.cast_le.mpr ( hM _ h ) ) ( by nlinarith [ le_max_left c M, le_max_right c M, pow_le_pow_right₀ ( show 1 ≤ |C| by rw [ abs_of_nonneg ] <;> linarith ) ( show g n ≥ 0 by positivity ) ] ) else by exact le_trans ( hc _ <| le_of_not_gt h ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| by positivity ) ⟩

/-
If f(n) is O(C^n) with 0 <= C <= 1, then f is polynomially bounded.
TODO: Show this holds for any LawfulGrowthRate instead.
-/
private lemma exp_subset_poly_of_le_one {f : ℕ → ℕ} {C : ℝ} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1)
    (hf : (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ))) : f ∈ GrowthRate.poly := by
  -- Since $0 \le C \le 1$, $C^n \le 1$ for all $n \ge 0$. Thus $f(n) = O(1)$.
  have h_f_one : (fun n ↦ (f n : ℝ)) =O[Filter.atTop] (fun n ↦ 1 : ℕ → ℝ) := by
    refine' hf.trans _;
    norm_num [ Asymptotics.isBigO_iff ];
    exact ⟨ 1, 0, fun n hn ↦ by rw [ abs_of_nonneg hC₀ ] ; exact pow_le_one₀ hC₀ hC₁ ⟩;
  -- Since $f(n)$ is $O(1)$, it is polynomially bounded.
  have h_f_poly : (fun n ↦ (f n : ℝ)) =O[Filter.atTop] (fun n ↦ (n : ℝ) ^ 0) := by
    grind;
  exact ⟨ 0, by simpa [ Asymptotics.isBigO_iff ] using h_f_poly ⟩

theorem exp_comp_log (hf : f ∈ exp) (hg : g ∈ log) : f ∘ g ∈ poly := by
  by_cases hC : ∃ C : ℝ, 1 < C ∧ (fun n ↦ (f n : ℝ)) =O[.atTop] (fun n ↦ C ^ (n : ℝ));
  · -- Apply `isBigO_comp_exp_of_isBigO_exp` to show `f(g(n)) = O(C^{g(n)})`.
    obtain ⟨C, hC₁, hC₂⟩ := hC;
    have h_f_g_poly : (fun n ↦ (f (g n) : ℝ)) =O[.atTop] (fun n ↦ C ^ (g n : ℝ)) := by
      apply isBigO_comp_exp_of_isBigO_exp hC₁.le hC₂;
    -- Apply `exists_pow_bound_of_exp_comp_log_real` to show `C^{g(n)} = O(n^K)` for some `K`.
    obtain ⟨K, hK⟩ : ∃ K : ℝ, (fun n ↦ C ^ (g n : ℝ)) =O[.atTop] (fun n ↦ (n : ℝ) ^ K) := by
      have := hg;
      rw [ log_iff_rlog ] at this;
      exact exists_pow_bound_of_exp_comp_log_real hC₁ this;
    have := h_f_g_poly.trans hK;
    convert poly_iff_rpow.mpr _;
    exact ⟨ K, this ⟩;
  · contrapose! hC;
    obtain ⟨ C, hC ⟩ := hf;
    rcases C with ( _ | _ | C ) <;> norm_num at *;
    · -- Since $0^n = 0$ for all $n > 0$, the condition $(fun n ↦ (f n : ℤ)) =O[Filter.atTop] (fun n ↦ 0 ^ n)$ implies that $f(n) = 0$ for all sufficiently large $n$.
      have h_f_zero : ∀ᶠ n in Filter.atTop, f n = 0 := by
        rw [ Asymptotics.isBigO_iff' ] at hC;
        norm_num +zetaDelta at *;
        obtain ⟨ c, hc, a, ha ⟩ := hC; exact ⟨ a + 1, fun n hn ↦ by simpa [ show n ≠ 0 by linarith ] using ha n ( by linarith ) ⟩ ;
      norm_num +zetaDelta at *;
      exact ⟨ 2, by norm_num, by rw [ Asymptotics.isBigO_iff ] ; exact ⟨ 1, by filter_upwards [ Filter.eventually_ge_atTop h_f_zero.choose ] with n hn; norm_num [ h_f_zero.choose_spec n hn ] ⟩ ⟩;
    · simp_all [ Filter.IsBoundedUnder, Filter.IsBounded ];
      obtain ⟨ b, a, hb ⟩ := hC;
      refine' ⟨ 2, by norm_num, _ ⟩;
      norm_num [ Asymptotics.isBigO_iff ];
      exact ⟨ b, a, fun n hn ↦ le_trans ( hb n hn ) ( le_mul_of_one_le_right ( by linarith [ show 0 ≤ b by exact le_trans ( Nat.cast_nonneg _ ) ( hb _ le_rfl ) ] ) ( one_le_pow₀ ( by norm_num ) ) ) ⟩;
    · refine' ⟨ C + 1 + 1, _, _ ⟩ <;> norm_cast;
      · linarith
      · norm_cast at *;
        rwa [Asymptotics.isBigO_iff] at hC ⊢

lemma exp_bound_nat {f : ℕ → ℕ} (hf : f ∈ GrowthRate.exp) :
    ∃ (C : ℕ) (M : ℕ), 1 < C ∧ ∀ n, f n ≤ M * C ^ n := by
      obtain ⟨C₀, hC₀, N, hN⟩ : ∃ C₀ M₀ N, ∀ n ≥ N, f n ≤ M₀ * C₀ ^ n := by
        obtain ⟨ C₀, hC₀ ⟩ := hf;
        norm_num [ Asymptotics.isBigO_iff ] at hC₀;
        obtain ⟨ c, a, hca ⟩ := hC₀; use C₀, ⌈c⌉₊, a; intro n hn; specialize hca n hn; exact_mod_cast ( by nlinarith [ Nat.le_ceil c, show ( C₀ ^ n : ℝ ) ≥ 0 by positivity ] : ( f n : ℝ ) ≤ ⌈c⌉₊ * C₀ ^ n ) ;
      -- Choose `C = max(C₀, 2)` to ensure `C > 1`.
      set C := max C₀ 2
      have hC : 1 < C := by
        exact lt_max_of_lt_right ( by decide );
      refine' ⟨ C, hC₀ + ∑ n ∈ Finset.range N, f n + 1, hC, fun n ↦ _ ⟩;
      by_cases hn : n < N;
      · nlinarith [ Nat.zero_le ( ∑ n ∈ Finset.range N, f n ), Finset.single_le_sum ( fun n _ ↦ Nat.zero_le ( f n ) ) ( Finset.mem_range.mpr hn ), pow_pos ( zero_lt_one.trans hC ) n ];
      · exact le_trans ( hN n ( le_of_not_gt hn ) ) ( Nat.mul_le_mul ( by nlinarith [ Nat.zero_le ( ∑ n ∈ Finset.range N, f n ) ] ) ( Nat.pow_le_pow_left ( le_max_left _ _ ) _ ) )

lemma polylog_bound_nat {g : ℕ → ℕ} (hg : g ∈ GrowthRate.polylog) :
    ∃ (k : ℕ) (K : ℕ), ∀ᶠ n in Filter.atTop, g n ≤ K * (Nat.log 2 n) ^ k := by
      obtain ⟨ k, hk ⟩ := hg;
      obtain ⟨ K, hK ⟩ := hk.exists_pos;
      simp_all [ Asymptotics.IsBigOWith ];
      exact ⟨ k, ⌈K⌉₊, hK.2.choose, fun n hn ↦ by exact_mod_cast ( by nlinarith [ Nat.le_ceil K, hK.2.choose_spec n hn, show ( Nat.log 2 n : ℝ ) ^ k ≥ 0 by positivity ] : ( g n : ℝ ) ≤ ⌈K⌉₊ * Nat.log 2 n ^ k ) ⟩

lemma quasipoly_of_bound_nat {h : ℕ → ℕ} {A k M : ℕ} (hA : 1 < A)
    (hh : ∀ᶠ n in Filter.atTop, h n ≤ M * A ^ ((Nat.log 2 n) ^ k)) : h ∈ GrowthRate.quasipoly := by
  -- Let $L = \log_2 A$. Then $A \leq 2^L$ (actually $A < 2^{L+1}$).
  set L := Nat.log 2 A
  -- We want to bound this by $2 ^ ((log n)^C)$.
  have h_bound : ∀ᶠ n in Filter.atTop, (h n : ℝ) ≤ M * 2 ^ ((L + 1) * (Nat.log 2 n) ^ k) := by
    filter_upwards [ hh ] with n hn
    have hA_le : (A : ℝ) ≤ 2 ^ (L + 1) := by
      exact_mod_cast Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ );
    grw [pow_mul, ← hA_le, hn]
    exact_mod_cast le_rfl
  -- We want to bound this by $2 ^ ((log n)^(k+1))$.
  have h_bound_final : ∀ᶠ n in Filter.atTop, (h n : ℝ) ≤ M * 2 ^ ((Nat.log 2 n) ^ (k + 1)) := by
    -- Since $(L + 1) * (Nat.log 2 n) ^ k \leq (Nat.log 2 n) ^ (k + 1)$ for large enough $n$, we can conclude.
    have h_ineq : ∀ᶠ n in Filter.atTop, (L + 1) * (Nat.log 2 n) ^ k ≤ (Nat.log 2 n) ^ (k + 1) := by
      have h_ineq : ∀ᶠ n in Filter.atTop, (L + 1) ≤ Nat.log 2 n := by
        exact Filter.eventually_atTop.mpr ⟨ 2 ^ ( L + 1 ), fun n hn ↦ Nat.le_log_of_pow_le ( by norm_num ) hn ⟩;
      filter_upwards [ h_ineq ] with n hn using by rw [ pow_succ' ] ; exact Nat.mul_le_mul_right _ hn;
    filter_upwards [ h_bound, h_ineq ] with n hn hn' using le_trans hn ( mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num ) hn' ) ( Nat.cast_nonneg _ ) );
  refine' ⟨ k + 1, _ ⟩;
  rw [ Asymptotics.isBigO_iff ];
  norm_num at *;
  exact ⟨M, h_bound_final.choose, fun n hn ↦ le_trans ( h_bound_final.choose_spec n hn ) ( by norm_num [ Norm.norm ] ) ⟩

theorem exp_comp_polylog (hf : f ∈ exp) (hg : g ∈ polylog) : f ∘ g ∈ quasipoly := by
  obtain ⟨C, M_f, hC, hf⟩ := exp_bound_nat hf
  obtain ⟨k, K, hg⟩ := polylog_bound_nat hg
  set K' := max 1 K;
  apply quasipoly_of_bound_nat (A := C ^ K') (k := k) (M := M_f)
  · exact one_lt_pow₀ hC ( by positivity );
  · simp +zetaDelta at *;
    exact ⟨ hg.choose, fun n hn ↦ le_trans ( hf _ ) ( by simpa only [ ← pow_mul ] using Nat.mul_le_mul_left _ ( pow_le_pow_right₀ hC.le <| by nlinarith [ hg.choose_spec n hn, Nat.le_max_left 1 K, Nat.le_max_right 1 K, pow_nonneg ( Nat.zero_le ( Nat.log 2 n ) ) k ] ) ) ⟩

theorem exp_comp_linear (hf : f ∈ exp) (hg : g ∈ linear) : f ∘ g ∈ exp := by
    -- From `hf`, we have some `C` such that `f n = O(C^n)`. We can assume `C ≥ 2` without loss of generality.
  obtain ⟨C, hC⟩ : ∃ C, (f · : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ n : ℕ → ℤ) ∧ 2 ≤ C := by
    rcases hf with ⟨ C, hC ⟩
    generalize_proofs at *;
    rcases C with ( _ | _ | C ) <;> norm_num at *;
    · refine' ⟨ 2, _, _ ⟩ <;> norm_num;
      exact hC.trans ( by simpa using Asymptotics.isBigO_of_le _ fun n ↦ by cases n <;> norm_num [ pow_succ' ] );
    · refine' ⟨ 2, _, _ ⟩ <;> norm_num [ Asymptotics.isBigO_iff ];
      obtain ⟨ c, hc ⟩ := hC;
      norm_num [ Norm.norm ] at *;
      exact ⟨ c, hc.choose, fun n hn ↦ le_trans ( hc.choose_spec n hn ) ( le_mul_of_one_le_right ( by exact le_trans ( Nat.cast_nonneg _ ) ( hc.choose_spec _ le_rfl ) ) ( one_le_pow₀ ( by norm_num ) ) ) ⟩;
    · exact ⟨ _, hC, by linarith ⟩;
  -- From `hg`, we have `g n = O(n)`. This implies there exists a constant `K` such that `g n ≤ K * n` eventually.
  obtain ⟨K, hK⟩ : ∃ K, ∀ᶠ n in .atTop, g n ≤ K * n := by
    obtain ⟨ K, hK ⟩ := Asymptotics.isBigO_iff.mp hg;
    norm_num at *;
    exact ⟨ ⌈K⌉₊, hK.choose, fun n hn ↦ by exact_mod_cast le_trans ( hK.choose_spec n hn ) ( mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ ) ) ⟩;
  -- Then `f (g n) = O(C^(g n))`.
  have hfg : (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ C ^ (g n) : ℕ → ℤ) := by
    simp_all [ Asymptotics.isBigO_iff' ];
    obtain ⟨ c, hc, a, ha ⟩ := hC.1;
    use c + ∑ x ∈ Finset.range (a + 1), (f x : ℝ) / ‖C‖ ^ x, by
      exact add_pos_of_pos_of_nonneg hc <| Finset.sum_nonneg fun _ _ ↦ div_nonneg ( Nat.cast_nonneg _ ) <| by positivity;, a + hK.choose + 1, by
      intro b hb; by_cases h : g b < a <;> simp_all [ add_mul ];
      · refine' le_add_of_nonneg_of_le ( by positivity ) _;
        rw [ Finset.sum_mul _ _ _ ];
        exact le_trans ( by rw [ div_mul_cancel₀ _ ( by exact ne_of_gt ( pow_pos ( norm_pos_iff.mpr ( by linarith ) ) _ ) ) ] ) ( Finset.single_le_sum ( fun i _ ↦ mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( norm_nonneg _ ) _ ) ) ( pow_nonneg ( norm_nonneg _ ) _ ) ) ( Finset.mem_range.mpr ( by linarith ) ) );
      · exact le_add_of_le_of_nonneg ( ha _ h ) ( mul_nonneg ( Finset.sum_nonneg fun _ _ ↦ by positivity ) ( by positivity ) );
  -- Since $C \geq 2$, the function $x \mapsto C^x$ is monotone increasing.
  have h_mono : (fun n ↦ C ^ (g n) : ℕ → ℤ) =O[.atTop] (fun n ↦ C ^ (K * n) : ℕ → ℤ) := by
    rw [ Asymptotics.isBigO_iff ];
    norm_num [ Norm.norm ];
    exact ⟨ 1, by rcases Filter.eventually_atTop.mp hK with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn ↦ by rw [ abs_of_nonneg ( by norm_cast; linarith ) ] ; exact le_trans ( pow_le_pow_right₀ ( by norm_cast; linarith ) ( hN n hn ) ) ( by norm_num ) ⟩ ⟩;
  -- Therefore, $f (g n) = O((C^K)^n)$.
  have h_comp : (fun n ↦ (f (g n) : ℤ)) =O[.atTop] (fun n ↦ (C^K) ^ n : ℕ → ℤ) := by
    simpa only [ pow_mul ] using hfg.trans h_mono;
  use C.natAbs^K;
  simpa [ abs_of_nonneg ( by linarith : 0 ≤ C ) ] using h_comp

lemma _root_.Nat.Primrec.sum_range (hf : Nat.Primrec f) : Nat.Primrec (fun n ↦ ∑ i ∈ Finset.range n, f i) := by
  -- Define g such that g(n, s) = s + f(n)
  let g : ℕ → ℕ → ℕ := fun n s ↦ s + f n;
  -- By definition of $g$, we know that $g$ is primitive recursive.
  have hg : Nat.Primrec (fun p ↦ g p.unpair.1 p.unpair.2) := by
    convert Nat.Primrec.add.comp (.pair (.right) (hf.comp .left)) using 1
    simp [g]
  -- By definition of $g$, we know that $S(n) = \text{Nat.rec} \ 0 \ (\lambda n \ s. s + f(n)) \ n$.
  have hS : (fun n ↦ ∑ i ∈ Finset.range n, f i) = fun n ↦ Nat.rec 0 (fun n s ↦ g n s) n := by
    funext n
    induction n
    · rfl
    · simp [*, Finset.sum_range_succ]
      rfl
  rw [hS]
  convert Nat.Primrec.prec1 0 hg using 1
  simp

/--
Every primitive recursive function is bounded by a monotone primitive recursive function.
-/
private lemma exists_monotone_primrec_bound {f : ℕ → ℕ} (hf : Nat.Primrec f) : ∃ g, Nat.Primrec g ∧ Monotone g ∧ ∀ n, f n ≤ g n := by
  -- Let $S(n) = \sum_{i=0}^{n} f(i)$.
  set S : ℕ → ℕ := fun n ↦ ∑ i ∈ Finset.range (n + 1), f i;
  use S;
  refine' ⟨ _, _, _ ⟩;
  · have h_sum := hf.sum_range
    exact h_sum.comp ( Nat.Primrec.succ );
  · exact fun n m hnm ↦ Finset.sum_le_sum_of_subset ( Finset.range_mono ( Nat.succ_le_succ hnm ) );
  · exact fun n ↦ Finset.single_le_sum ( fun i _ ↦ Nat.zero_le ( f i ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_self n ) )

theorem primitiveRecursive_comp (hf : f ∈ primitiveRecursive) (hg : g ∈ primitiveRecursive) :
    f ∘ g ∈ primitiveRecursive := by
  obtain ⟨ h_f, hf_primrec, hf_bound ⟩ := hf
  obtain ⟨ h_g, hg_primrec, hg_bound ⟩ := hg;
  -- Apply the lemma that allows bounding a primitive recursive function by a monotone one to $h_f$.
  obtain ⟨ H_f, hH_f_primrec, hH_f_mono, hH_f_bound ⟩ := exists_monotone_primrec_bound hf_primrec;
  -- Thus $f(g(n)) \le C_f H_f(g(n)) + K$.
  obtain ⟨ C_f, N_f, hf_bound ⟩ : ∃ C_f N_f, ∀ x ≥ N_f, f x ≤ C_f * H_f x := by
    have := hf_bound;
    obtain ⟨ C_f, N_f, hC_f ⟩ := this.exists_pos;
    rw [ Asymptotics.isBigOWith_iff ] at hC_f;
    norm_num at *;
    obtain ⟨ N_f, hN_f ⟩ := hC_f;
    exact ⟨ ⌈C_f⌉₊, N_f, fun x hx ↦ by have := hN_f x hx; exact_mod_cast this.trans ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr ( hH_f_bound x ) ) ( by positivity ) ) |> le_trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| Nat.cast_nonneg _ ⟩
  obtain ⟨ C_g, N_g, hg_bound ⟩ : ∃ C_g N_g, ∀ n ≥ N_g, g n ≤ C_g * h_g n := by
    have := hg_bound;
    unfold GrowthRate.bigO at this;
    rw [ Set.mem_setOf_eq, Asymptotics.isBigO_iff' ] at this;
    norm_num at *;
    obtain ⟨ c, hc₀, N_g, hc ⟩ := this; exact ⟨ ⌈c⌉₊, N_g, fun n hn ↦ by exact_mod_cast hc n hn |> le_trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| Nat.cast_nonneg _ ⟩ ;
  obtain ⟨ K, hK ⟩ : ∃ K, ∀ x < N_f, f x ≤ K := by
    exact ⟨ Finset.sup ( Finset.range N_f ) f, fun x hx ↦ Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hx ) ⟩;
  -- Thus for $n \ge N_g$, $f(g(n)) \le C_f H_f(C_g h_g(n)) + K$.
  have h_comp_bound : ∀ n ≥ N_g, f (g n) ≤ C_f * H_f (C_g * h_g n) + K := by
    intros n hn
    by_cases hgn : g n < N_f;
    · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( hK _ hgn );
    · exact le_add_of_le_of_nonneg ( le_trans ( hf_bound _ ( le_of_not_gt hgn ) ) ( Nat.mul_le_mul_left _ ( hH_f_mono ( hg_bound _ hn ) ) ) ) ( Nat.zero_le _ );
  -- The function $B(n) = C_f H_f(C_g h_g(n)) + K$ is primitive recursive (composition, sum, product of primrec functions).
  have hB_primrec : Nat.Primrec (fun n ↦ C_f * H_f (C_g * h_g n) + K) := by
    have hB_primrec : Nat.Primrec (fun n ↦ H_f (C_g * h_g n)) := by
      have hB_primrec : Nat.Primrec (fun n ↦ C_g * h_g n) := by
        have hB_primrec : Nat.Primrec (fun n ↦ C_g * n) := by
          have h_mul : Nat.Primrec (Nat.unpaired (· * ·)) := by
            exact Nat.Primrec.mul
          convert h_mul.comp ( Nat.Primrec.const C_g |> Nat.Primrec.pair <| Nat.Primrec.id ) using 1;
          aesop;
        exact hB_primrec.comp hg_primrec;
      exact hH_f_primrec.comp hB_primrec;
    have hB_primrec : Nat.Primrec (fun n ↦ C_f * n) := by
      have h_mul : Nat.Primrec (fun n ↦ n * C_f) := by
        have h_mul_step : ∀ m, Nat.Primrec (fun n ↦ n * m) := by
          intro m; induction m <;> simp_all [ Nat.mul_succ, Nat.Primrec.const ] ;
          rename_i k hk;
          convert Nat.Primrec.add.comp ( hk.pair Nat.Primrec.id ) using 1;
          exact funext fun n ↦ by simp [ Nat.unpair_pair ] ;
        exact h_mul_step C_f;
      simpa only [ mul_comm ] using h_mul;
    have hB_primrec : Nat.Primrec (fun n ↦ C_f * H_f (C_g * h_g n)) := by
      exact hB_primrec.comp ‹_›;
    have hB_primrec : Nat.Primrec (fun n ↦ n + K) := by
      exact Nat.recOn K ( by exact Nat.Primrec.id ) fun n ihn ↦ by exact Nat.Primrec.succ.comp ihn;
    exact hB_primrec.comp ‹_›;
  refine' ⟨ _, hB_primrec, _ ⟩;
  refine' Asymptotics.IsBigO.of_bound 1 _;
  simp +zetaDelta at *;
  exact ⟨ N_g, fun n hn ↦ by erw [ Real.norm_of_nonneg ( by positivity ) ] ; exact_mod_cast h_comp_bound n hn ⟩

section computable

/-
`max_scan f n` computes the maximum value of `f` on `0..n`. It is defined recursively: `max_scan f 0 = f 0`, and `max_scan f (n+1) = max (max_scan f n) (f (n+1))`.
-/
private def max_scan (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (f 0) (fun k acc ↦ max acc (f (k + 1))) n

private lemma max_scan_le (n : ℕ) : f n ≤ max_scan f n := by
  induction n <;> simp [ *, max_scan ]

private lemma max_scan_mono (f : ℕ → ℕ) : Monotone (max_scan f) := by
  exact monotone_nat_of_le_succ fun k ↦ by unfold max_scan; aesop;

private lemma computable_max_scan {f : ℕ → ℕ} (hf : Computable f) : Computable (max_scan f) := by
  convert Computable.nat_rec _ _ _;
  rotate_left;
  exact fun _ ↦ f 0;
  exact fun _ p ↦ Nat.max p.2 ( f ( p.1 + 1 ) );
  · exact Computable.id;
  · exact Computable.const _;
  · -- The function p ↦ p.2.max (f (p.1 + 1)) is computable because it is a composition of computable functions.
    have h_max : Computable₂ (fun (p : ℕ × ℕ) (q : ℕ × ℕ) ↦ Nat.max p.2 q.2) := by
      have h_max : Computable₂ (fun (p q : ℕ) ↦ Nat.max p q) := by
        -- The maximum function is primitive recursive, and primitive recursive functions are computable.
        have h_max_primrec : Primrec₂ (fun p q : ℕ ↦ p.max q) := by
          exact Primrec.nat_max;
        exact Primrec₂.to_comp h_max_primrec;
      exact h_max.comp (Computable.snd.comp (Computable.fst)) (Computable.snd.comp (Computable.snd));
    convert h_max.comp₂ _ _ using 1;
    rotate_left;
    exact fun _ p ↦ ( p.1, p.2 );
    exact fun _ p ↦ ( p.1, f ( p.1 + 1 ) );
    · exact Computable.pair ( Computable.fst.comp Computable.snd ) ( Computable.snd.comp Computable.snd );
    · exact Computable.pair ( Computable.fst.comp ( Computable.snd.comp Computable.id ) ) ( hf.comp ( Computable.succ.comp ( Computable.fst.comp ( Computable.snd.comp Computable.id ) ) ) );
    · rfl;
  · exact rfl

lemma bigO_implies_bound {f g : ℕ → ℕ} (h : f ∈ GrowthRate.bigO g) :
    ∃ C K, ∀ n, f n ≤ C * g n + K := by
  obtain ⟨ C, hC ⟩ := h.exists_pos;
  rw [ Asymptotics.IsBigOWith ] at hC;
  norm_num at *;
  -- Let $K$ be the maximum of $f(n)$ for $n < N$.
  obtain ⟨K, hK⟩ : ∃ K, ∀ n < hC.right.choose, f n ≤ K := by
    exact ⟨ Finset.sup ( Finset.range hC.2.choose ) f, fun n hn ↦ Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hn ) ⟩;
  exact ⟨ ⌈C⌉₊, K, fun n ↦ if hn : n < hC.2.choose then le_trans ( hK n hn ) ( by norm_num ) else by have := hC.2.choose_spec n ( le_of_not_gt hn ) ; exact_mod_cast ( by nlinarith [ Nat.le_ceil C, show ( g n : ℝ ) ≥ 0 by positivity ] : ( f n : ℝ ) ≤ ⌈C⌉₊ * g n + K ) ⟩

lemma bound_implies_bigO {f g : ℕ → ℕ} (C K : ℕ) (h : ∀ n, f n ≤ C * g n + K) :
    f ∈ GrowthRate.bigO (fun n ↦ g n + 1) := by
  simp [GrowthRate.bigO, Asymptotics.isBigO_iff]
  use C + K + 1, 0
  exact fun n hn ↦ by erw [ Real.norm_of_nonneg ( by positivity ) ] ; norm_cast; nlinarith [ h n ]

lemma exists_monotone_computable_bound {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F, Computable F ∧ Monotone F ∧ f ∈ GrowthRate.bigO F := by
  refine ⟨max_scan f, computable_max_scan hf, max_scan_mono f, ?_⟩
  apply Asymptotics.IsBigO.of_bound 1
  norm_num
  exact ⟨0, fun n hn ↦ max_scan_le n⟩

/--
The function `n ↦ C * n + K` is computable.
-/
private lemma computable_affine (C K : ℕ) : Computable (fun n ↦ C * n + K) := by
  apply Computable.comp (f := fun n ↦ n + K) (g := fun n ↦ C * n)
  · induction K
    · exact Computable.id
    simp [Nat.add_comm, Nat.add_left_comm] at *
    exact Computable.comp ‹_› Computable.succ
  · apply Primrec.to_comp
    induction C
    · simp [Primrec.const]
    simp_rw [Nat.succ_mul]
    exact Primrec.nat_add.comp ‹_› Primrec.id

theorem computable_comp (hf : f ∈ computable) (hg : g ∈ computable) :
    f ∘ g ∈ computable := by
  obtain ⟨f', hf', hf⟩ := hf
  obtain ⟨g', hg', hg⟩ := hg
  obtain ⟨F, hF₁, hF₂⟩ := GrowthRate.exists_monotone_computable_bound hf'
  obtain ⟨C₁, K₁, hC₁⟩ := bigO_implies_bound hg
  obtain ⟨C₂, K₂, hC₂⟩ := GrowthRate.bigO_implies_bound ( hf.trans hF₂.2 )
  -- Define H(n) = C₂ * F(C₁ * g'(n) + K₁) + K₂.
  set H : ℕ → ℕ := fun n ↦ C₂ * F (C₁ * g' n + K₁) + K₂;
  refine ⟨H, ?_, ?_⟩
  · exact (computable_affine _ _).comp <| hF₁.comp <| (computable_affine _ _).comp hg'
  have hfg_le_H : ∀ n, f (g n) ≤ H n := by
    exact fun n ↦ le_trans ( hC₂ _ ) ( by exact add_le_add_right ( mul_le_mul_of_nonneg_left ( hF₂.1 ( hC₁ _ ) ) ( Nat.zero_le _ ) ) _ ) ;
  simp_rw [bigO, Set.mem_setOf_eq, Asymptotics.isBigO_iff, Filter.eventually_atTop]
  use 1, 0
  exact fun n hn ↦ by simpa using hfg_le_H n

end computable

end closure_comp

end GrowthRate
