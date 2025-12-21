import CircuitComp.NC

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Ideal

open FeedForward
open CircuitFamily

/-!
Defines the class AC₀, which is typically defined as constant-depth boolean circuits with
arbitrary fan-in AND and OR gates, and NOT gates.
We define it as circuits with arbitrary fan-in AND, and NOT gates (at any layer).

Also define `ACi`, which is like AC₀ but has `log(n)^i` depth. `AC` is the union of all `ACi`.

# Theorems
 * These are equivalent definitions
 * AC₀ cannot compute the Parity function

# References
[www.tu-chemnitz.de](https://www.tu-chemnitz.de/informatik/theoretische-informatik/publications/2013-RANDOM-CNF-sensitivity.pdf_
[cs.washington.edu](https://homes.cs.washington.edu/~anuprao/pubs/CSE531Winter12/lecture10.pdf)

-/

def AC₀_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Fin 0, 1⟩, --Constant one
  ⟨Fin 1, fun x ↦ 1 - x 0⟩} --NOT
  ∪
  ⋃ n, {⟨Fin n, fun x ↦ ∏ i, x i⟩} --ANDs of all arity (including Id)

/-- AC₀, the constant-depth polynomial-size circuits of NOT gates and arbitrary-arity AND gates. -/
def AC₀ : Set (FuncFamily (Fin 2)) :=
  CircuitClass .poly .const AC₀_GateOps

/-- The circuit class of nonuniform ACi: polynomial-size circuits with
NOTs and arbitrary fan-in ANDs, and depth O(logⁱ n). -/
def ACi (i : ℕ) : Set (FuncFamily (Fin 2)) :=
  CircuitClass .poly (.bigO (Nat.log2 · ^ i)) AC₀_GateOps

/-- AC₀ is the 0th element of the ACi hierarchy -/
theorem ACi_zero : ACi 0 = AC₀ := by
  rfl

def AC : Set (FuncFamily (Fin 2)) :=
  ⋃ i, ACi i

theorem ACi_subset_NC (i : ℕ) : ACi i ⊆ AC :=
  Set.subset_iUnion_of_subset i fun _ ↦ id

/-- The class NC₀ is contained in AC₀. -/
theorem NC₀_subset_AC₀ : NC₀ ⊆ AC₀ := by
  apply CircuitClass.Monotone_gates
  intro
  simp only [NC₀_GateOps, AC₀_GateOps, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.iUnion_singleton_eq_range]
  rintro (rfl|rfl|rfl|rfl)
  · simp
  · right
    use 1
    simp
  · simp
  · right
    use 2
    simp

/-- The AND problem is contained in AC₀, because we can take a single AND gate. -/
theorem AND_mem_AC₀ : FuncFamily.AND ∈ AC₀ := by
  use (fun n ↦ ⟨
    1,
    ![Fin n, Fin 1],
    fun d h ↦ ⟨⟨Fin n, fun x ↦ ∏ i, x i⟩, by rw [Fin.fin_one_eq_zero d]; exact id⟩,
    rfl,
    rfl
  ⟩)
  and_intros
  · intro
    ext
    rfl
  · intro n
    rw [FeedForward.finite]
    simp only [Fin.isValue, Fin.castSucc_zero, Matrix.cons_val_zero, eq_mpr_eq_cast, Nat.reduceAdd]
    intro i
    fin_cases i <;> simp <;> infer_instance
  · use 0
    simp [-Asymptotics.isBigO_one_iff, size]
  · simp [-Asymptotics.isBigO_one_iff, hasDepth, GrowthRate.const, GrowthRate.bigO]
  · simp only [CircuitFamily.onlyUsesGates, FeedForward.onlyUsesGates]
    intro n d _
    simp only [AC₀_GateOps, Fin.isValue, Set.iUnion_singleton_eq_range]
    right
    use n

theorem NC₀_ssubset_AC₀ : NC₀ ⊂ AC₀ := by
  refine ssubset_of_ne_of_subset ?_ NC₀_subset_AC₀
  exact (ne_of_mem_of_not_mem' AND_mem_AC₀ AND_not_mem_NC₀).symm

/- Sketch that we can approximate AC₀ well by low-degree polynomials
  --Induction on depth
  --If the final gate is a NOT: use 1-P
  --If the final gate is an AND: use 1 - Π_{k=ℓ} (1 - (∑_{i∈Sₖ} P_i)^2 ) where we pick ℓ random
  -- sets Sₖ. See https://homes.cs.washington.edu/~anuprao/pubs/CSE531Winter12/lecture10.pdf
-/

/-- If the final gate of an AC₀ circuit is an OR gate, and we have good low-degree
approximations over 𝔽₃ for each of its inputs, then this computes a good approximation
of the whole circuit, given ℓ uniformly random subsets S. -/
noncomputable def approxOr {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod 3)) (S : Fin ℓ → Finset (Fin width)) :
    MvPolynomial (Fin vars) (ZMod 3) :=
  1 - ∏ k, (1 - (∑ i ∈ S k, polys i)^2)

/-- The `approxOr` doesn't increase the degree too much, just by a factor of 2ℓ. -/
theorem approxOr_totalDegree (vars width ℓ : ℕ)
  (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod 3)) (S : Fin ℓ → Finset (Fin width)) :
    (approxOr polys S).totalDegree ≤ 2 * ℓ * ⨆ i, (polys i).totalDegree := by
  have h_term (k) : (1 - (∑ i ∈ S k, polys i)^2).totalDegree ≤ 2 * (⨆ i, (polys i).totalDegree) := by
    grw [MvPolynomial.totalDegree_sub]
    simp only [MvPolynomial.totalDegree_one, zero_le, sup_of_le_right]
    grw [MvPolynomial.totalDegree_pow]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    grw [MvPolynomial.totalDegree_finsetSum_le]
    intro i a
    exact le_ciSup (Set.finite_range (polys · |>.totalDegree) |> Set.Finite.bddAbove) i
  trans (∑ k, (1 - (∑ i ∈ S k, polys i)^2).totalDegree)
  · grw [approxOr, MvPolynomial.totalDegree_sub, MvPolynomial.totalDegree_finset_prod]
    simp
  · grw [Finset.sum_le_sum fun i _ ↦ h_term i]
    simp [mul_assoc, mul_comm]
/-
For any non-zero vector v in (ZMod 3)^n, at most half of the subsets of indices sum to 0. This can be proven by picking an index i where v_i ≠ 0 and pairing each subset S not containing i with S ∪ {i}. In each pair, at most one subset can sum to 0.
-/
lemma subset_sum_zero_bound {n : ℕ} (v : Fin n → ZMod 3) (hv : v ≠ 0) :
    2 * (Finset.univ.filter (fun s : Finset (Fin n) => ∑ i ∈ s, v i = 0)).card ≤ (Finset.univ : Finset (Finset (Fin n))).card := by
  obtain ⟨ i, hi ⟩ := Function.ne_iff.mp hv;
  -- Let's count the number of subsets where the sum is zero by considering pairs of subsets that differ only by the inclusion of i.
  have h_pairs : Finset.card (Finset.filter (fun s => ∑ i ∈ s, v i = 0) (Finset.powerset (Finset.univ : Finset (Fin n)))) ≤ Finset.card (Finset.filter (fun s => ∑ i ∈ s, v i ≠ 0) (Finset.powerset (Finset.univ : Finset (Fin n)))) := by
    have h_pairs : Finset.filter (fun s => ∑ i ∈ s, v i = 0) (Finset.powerset (Finset.univ : Finset (Fin n))) ⊆ Finset.image (fun s => if i ∈ s then s \ {i} else s ∪ {i}) (Finset.filter (fun s => ∑ i ∈ s, v i ≠ 0) (Finset.powerset (Finset.univ : Finset (Fin n)))) := by
      intro s hs
      simp_all
      use if i ∈ s then s \ { i } else Insert.insert i s; aesop;
    exact le_trans ( Finset.card_le_card h_pairs ) ( Finset.card_image_le );
  have := Finset.card_add_card_compl ( Finset.filter ( fun s : Finset ( Fin n ) => ∑ i ∈ s, v i = 0 ) ( Finset.powerset ( Finset.univ : Finset ( Fin n ) ) ) ) ; simp_all +decide [ Finset.filter_not, Finset.card_sdiff ] ; linarith

/-
The number of tuples where a predicate holds for all components is the power of the number of elements where it holds. This is a standard counting argument: the set of such functions is isomorphic to the set of functions from ι to the subtype {b // P b}, which has cardinality |{b // P b}|^|ι|.
-/
lemma tuple_fail_count {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β] (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun (f : ι → β) => ∀ i, P (f i))).card = (Finset.univ.filter P).card ^ Fintype.card ι := by
      have h_count : {f : ι → β | ∀ i, P (f i)} ≃ (ι → {b : β | P b}) := by
        exact ⟨ fun f => fun i => ⟨ f.val i, f.property i ⟩, fun f => ⟨ _, fun i => ( f i ).2 ⟩, fun f => rfl, fun f => rfl ⟩;
      have := Fintype.card_congr h_count;
      simp_all +decide [ Fintype.card_pi, Fintype.card_subtype ]

/-
A probabilistic method averaging argument: if for every bad input, the number of failing witnesses is at most |β|/C, then there exists a witness that fails on at most |Bad|/C inputs.
Proof: Consider the sum of indicators of failures over Bad x β.
∑_{a ∈ Bad} |{b | Fail a b}| ≤ |Bad| * (|β|/C).
Swap sums: ∑_{b ∈ β} |{a ∈ Bad | Fail a b}| ≤ |Bad| * |β| / C.
The average number of failures per b is ≤ |Bad|/C.
Thus there exists b with number of failures ≤ |Bad|/C.
-/
open Finset

lemma prob_method_averaging {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    (Bad : Finset α) (Fail : α → β → Prop) [∀ a b, Decidable (Fail a b)]
    (C : ℕ)
    (h_prob : ∀ a ∈ Bad, (univ.filter (Fail a ·)).card * C ≤ Fintype.card β) :
    ∃ (b : β), (univ.filter (fun a => a ∈ Bad ∧ Fail a b)).card * C ≤ Bad.card := by
      by_contra! h;
      -- Let's consider the sum of the cardinalities of the sets {a ∈ Bad | Fail a b} over all b in β.
      have h_sum : ∑ b : β, (Finset.card (Finset.filter (fun a => a ∈ Bad ∧ Fail a b) Finset.univ)) = ∑ a ∈ Bad, (Finset.card (Finset.filter (fun b => Fail a b) Finset.univ)) := by
        simp +decide only [card_filter];
        rw [ Finset.sum_comm ];
        rw [ ← Finset.sum_subset ( Finset.subset_univ Bad ) ] <;> aesop;
      have := Finset.sum_le_sum fun b ( _ : b ∈ Finset.univ ) => Nat.mul_le_mul_right C ( h b );
      simp_all +decide [ ← Finset.sum_mul _ _ _ ];
      -- By combining the results from h_sum and this, we can derive the desired inequality.
      have h_combined : Fintype.card β * (#Bad + 1) ≤ (∑ a ∈ Bad, #{b : β | Fail a b}) * C := by
        cases C <;> aesop;
      have h_combined : (∑ a ∈ Bad, #{b : β | Fail a b}) * C ≤ Fintype.card β * #Bad := by
        exact le_trans ( Finset.sum_mul _ _ _ |> le_of_eq ) ( by simpa [ mul_comm ] using Finset.sum_le_sum fun a ha => h_prob a ha );
      nlinarith [ Fintype.card_pos_iff.mpr ‹_› ]

/-
Define the value of the approximation function for a given input vector v and random sets S.
-/
open MvPolynomial Finset

def approxOr_val {width ℓ : ℕ} (v : Fin width → ZMod 3) (S : Fin ℓ → Finset (Fin width)) : ZMod 3 :=
  1 - ∏ k, (1 - (∑ i ∈ S k, v i)^2)

/-
Define the value of the logical OR function over ZMod 3.
-/
open MvPolynomial Finset

def OR_val {width : ℕ} (v : Fin width → ZMod 3) : ZMod 3 :=
  1 - ∏ k, (1 - (v k)^2)

/-
The evaluation of the polynomial `approxOr` is equal to the `approxOr_val` function applied to the evaluations of the input polynomials. This follows from the fact that evaluation is a ring homomorphism.
-/
lemma approxOr_eval_eq {vars width ℓ : ℕ} (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod 3))
    (S : Fin ℓ → Finset (Fin width)) (y : Fin vars → ZMod 3) :
    (approxOr polys S).eval y = approxOr_val (fun i ↦ (polys i).eval y) S := by
      unfold approxOr approxOr_val; aesop;

/-
The approximation fails (value differs from OR) if and only if the input vector is non-zero AND for all chosen subsets, the sum of components is zero.
Proof:
If v = 0, then OR_val v = 0 and approxOr_val v S = 0 (since all sums are 0). So no failure.
If v ≠ 0, then OR_val v = 1. Failure means approxOr_val v S = 0.
approxOr_val v S = 1 - ∏ (1 - (sum)^2).
This is 0 iff the product is 1.
The product is 1 iff each factor (1 - (sum)^2) is 1.
(1 - x^2) = 1 in ZMod 3 iff x^2 = 0 iff x = 0.
So failure iff all sums are 0.
-/
lemma approxOr_failure_iff {width ℓ : ℕ} (v : Fin width → ZMod 3) (S : Fin ℓ → Finset (Fin width)) :
    approxOr_val v S ≠ OR_val v ↔ (v ≠ 0 ∧ ∀ k, ∑ i ∈ S k, v i = 0) := by
      unfold approxOr_val OR_val;
      by_cases h : v = 0 <;> simp_all
      constructor;
      · intro h_prod k;
        contrapose! h_prod; simp_all
        have : ∀ x : ZMod 3, x ≠ 0 → (1 - x ^ 2) = 0 := by
          native_decide;
        rw [ Finset.prod_eq_zero ( Finset.mem_univ k ) ( this _ h_prod ), Finset.prod_eq_zero ( Finset.mem_univ ( Classical.choose ( Function.ne_iff.mp h ) ) ) ( this _ ( Classical.choose_spec ( Function.ne_iff.mp h ) |> fun h => by aesop ) ) ];
      · intro hsum_zero
        have h_prod_zero : ∏ k : Fin width, (1 - v k ^ 2) = 0 := by
          -- Since $v$ is not the zero vector, there exists some $k$ such that $v k \neq 0$. In $ZMod 3$, the non-zero elements are $1$ and $2$. If $v k$ is $1$ or $2$, then $v k^2$ is $1$, so $1 - v k^2$ is $0$. Therefore, the product includes a zero term, making the entire product zero.
          obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
            exact Function.ne_iff.mp h;
          have h_prod_zero : ∃ k, v k ≠ 0 ∧ v k ^ 2 = 1 := by
            have h_prod_zero : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 = 1 := by
              native_decide;
            exact ⟨ k, hk, h_prod_zero _ hk ⟩;
          exact Finset.prod_eq_zero ( Finset.mem_univ h_prod_zero.choose ) ( by simp ( config := { decide := Bool.true } ) [ h_prod_zero.choose_spec ] );
        aesop

/-
For any non-zero input vector, the number of bad choices of `S` (causing failure) is at most `Total / 2^ℓ`. This follows from `subset_sum_zero_bound` and `tuple_fail_count`.
Proof:
Failure iff `∀ k, ∑ i ∈ S k, v i = 0`.
The number of such `S` is `(count {s | ∑ i ∈ s, v i = 0})^ℓ`.
By `subset_sum_zero_bound`, `count {s | ∑ i ∈ s, v i = 0} ≤ 2^width / 2`.
So `count bad S ≤ (2^width / 2)^ℓ = (2^width)^ℓ / 2^ℓ = Total / 2^ℓ`.
-/
lemma count_bad_S {width ℓ : ℕ} (v : Fin width → ZMod 3) (hv : v ≠ 0) :
    (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) => approxOr_val v S ≠ OR_val v)).card * 2^ℓ ≤ Fintype.card (Fin ℓ → Finset (Fin width)) := by
      by_cases h_subset_zero_bound : 2 * (Finset.univ.filter (fun (s : Finset (Fin width)) => ∑ i ∈ s, v i = 0)).card ≤ Fintype.card (Finset (Fin width));
      · have h_card_bad_S : (Finset.univ.filter (fun (S : Fin ℓ → Finset (Fin width)) => ∀ k, ∑ i ∈ S k, v i = 0)).card ≤ (Fintype.card (Finset (Fin width))) ^ ℓ / 2 ^ ℓ := by
          have h_card_bad_S : (Finset.univ.filter (fun (S : Fin ℓ → Finset (Fin width)) => ∀ k, ∑ i ∈ S k, v i = 0)).card = (Finset.univ.filter (fun (s : Finset (Fin width)) => ∑ i ∈ s, v i = 0)).card ^ ℓ := by
            convert tuple_fail_count ( fun s => ∑ i ∈ s, v i = 0 ) using 1;
            convert rfl;
            norm_num;
          rw [ Nat.le_div_iff_mul_le ( by positivity ) ] ; convert Nat.pow_le_pow_left h_subset_zero_bound ℓ using 1
          ring_nf
          congr! 1;
        refine' le_trans ( Nat.mul_le_mul_right _ ( _ : _ ≤ _ ) ) _;
        exact Fintype.card ( Finset ( Fin width ) ) ^ ℓ / 2 ^ ℓ;
        · convert h_card_bad_S using 2;
          ext; simp +decide [ approxOr_failure_iff, hv ] ;
        · norm_num [ Fintype.card_pi ];
          exact Nat.div_mul_le_self _ _;
      · exact False.elim <| h_subset_zero_bound <| by simpa using subset_sum_zero_bound v hv;

/-- By the union bound, there are some sets S such that `approxOr` is the logical OR
of the inputs on almost all valuations. -/
theorem exists_good_approxOr (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod 3)) :
    ∃ (S : Fin ℓ → Finset (Fin width)),
      { x : Fin vars → Fin 2 |
        let y : Fin vars → ZMod 3 := (fun i ↦ (x i : ZMod 3))
        (approxOr polys S).eval y = 1 - (∏ k, (1 - ((polys k).eval y) ^ 2))
      }.ncard ≥ (1 - 2^(-ℓ : ℤ) : ℚ) * 2^vars := by
  -- By the properties of the probabilistic method, we can find such an $S$.
  have h_prob : ∃ S : Fin ℓ → Finset (Fin width), (Finset.univ.filter (fun x : Fin vars → Fin 2 => approxOr_val (fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)) S ≠ OR_val (fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)))).card * 2^ℓ ≤ 2^vars := by
    -- Let's denote the set of bad inputs by `Bad`.
    set Bad := Finset.univ.filter (fun x : Fin vars → Fin 2 => ¬(fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)) = 0);
    -- By the properties of the probabilistic method, we can find such an $S$ for the set `Bad`.
    have h_prob : ∃ S : Fin ℓ → Finset (Fin width), (Finset.univ.filter (fun x : Fin vars → Fin 2 => x ∈ Bad ∧ approxOr_val (fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)) S ≠ OR_val (fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)))).card * 2^ℓ ≤ Bad.card := by
      apply_rules [ prob_method_averaging ];
      intro x hx;
      convert count_bad_S _ _;
      exact Finset.mem_filter.mp hx |>.2;
    obtain ⟨ S, hS ⟩ := h_prob;
    use S;
    refine le_trans ?_ ( hS.trans ?_ );
    · gcongr;
      intro x hx; by_cases hx' : ( fun i => MvPolynomial.eval ( fun i => ( x i : ZMod 3 ) ) ( polys i ) ) = 0 <;> simp_all +decide [ funext_iff ] ;
      · exact False.elim <| hx <| by unfold approxOr_val OR_val; norm_num;
      · exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun h => hx' |> fun ⟨ i, hi ⟩ => hi <| by simpa using congr_fun h i ⟩;
    · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num [ Finset.card_univ ] );
  obtain ⟨ S, hS ⟩ := h_prob;
  have h_card : (Finset.univ.filter (fun x : Fin vars → Fin 2 => approxOr_val (fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)) S = OR_val (fun i => MvPolynomial.eval (fun i => (x i : ZMod 3)) (polys i)))).card ≥ (2^vars : ℚ) - (2^vars : ℚ) / 2^ℓ := by
    rw [ sub_div', ge_iff_le, div_le_iff₀ ] <;> norm_cast;
    · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ show 0 < 2 ^ ℓ by positivity, show 0 < 2 ^ vars by positivity, show Finset.card ( Finset.filter ( fun x : Fin vars → Fin 2 => approxOr_val ( fun i => MvPolynomial.eval ( fun i => ( x i : ZMod 3 ) ) ( polys i ) ) S = OR_val ( fun i => MvPolynomial.eval ( fun i => ( x i : ZMod 3 ) ) ( polys i ) ) ) Finset.univ ) + Finset.card ( Finset.filter ( fun x : Fin vars → Fin 2 => ¬approxOr_val ( fun i => MvPolynomial.eval ( fun i => ( x i : ZMod 3 ) ) ( polys i ) ) S = OR_val ( fun i => MvPolynomial.eval ( fun i => ( x i : ZMod 3 ) ) ( polys i ) ) ) Finset.univ ) = 2 ^ vars from by rw [ Finset.filter_card_add_filter_neg_card_eq_card ] ; norm_num [ Finset.card_univ ] ];
    · positivity;
    · positivity;
  use S
  simp_all +decide [ Set.ncard_eq_toFinset_card' ];
  norm_num [ approxOr_eval_eq ] at *;
  norm_num [ OR_val ] at * ; ring_nf at * ; linarith

/-- Similarly, there is a polynomial of suitably low depth that computes AND. -/
theorem exists_good_approxAnd (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod 3)) :
    ∃ (approxAnd : MvPolynomial (Fin vars) (ZMod 3)),
        approxAnd.totalDegree ≤ 2 * ℓ * ⨆ i, (polys i).totalDegree ∧
      { x : Fin vars → Fin 2 |
        let y : Fin vars → ZMod 3 := (fun i ↦ (x i : ZMod 3))
        approxAnd.eval y = (∏ k, ((polys k).eval y)^2)
      }.ncard ≥ (1 - 2^(-ℓ : ℤ) : ℚ) * 2^vars := by
  obtain ⟨S, hS⟩ := exists_good_approxOr vars width ℓ polys
  have h_P_OR_eval := approxOr_eval_eq polys S
  have h_P_OR_deg := approxOr_totalDegree vars width ℓ polys S
  set P_OR := approxOr polys S
  sorry

noncomputable section AristotleLemmas

lemma AC₀_GateOps_cases {op : FeedForward.GateOp (Fin 2)} (h : op ∈ AC₀_GateOps) :
    op = ⟨Fin 0, 1⟩ ∨
    op = ⟨Fin 1, fun x ↦ 1 - x 0⟩ ∨
    ∃ n, op = ⟨Fin n, fun x ↦ ∏ i, x i⟩ := by
      unfold AC₀_GateOps at h ; aesop;

lemma exists_poly_for_gate {n ℓ : ℕ}
    (op : FeedForward.GateOp (Fin 2)) (hop : op ∈ AC₀_GateOps)
    (polys : op.ι → MvPolynomial (Fin n) (ZMod 3)) :
    ∃ (P : MvPolynomial (Fin n) (ZMod 3)) (Bad : Set (Fin n → Fin 2)),
      P.totalDegree ≤ 2 * ℓ * (⨆ i, (polys i).totalDegree) ∧
      (Bad.ncard : ℚ) ≤ (2^n : ℚ) * (2 : ℚ)^(-ℓ : ℤ) ∧
      ∀ x : Fin n → Fin 2, x ∉ Bad →
        let inputs := fun i ↦ (polys i).eval (fun j ↦ ((x j : Nat) : ZMod 3))
        (∀ i, inputs i ∈ ({0, 1} : Set (ZMod 3))) →
        P.eval (fun j ↦ ((x j : Nat) : ZMod 3)) = (op.func (fun i ↦ if inputs i = 1 then 1 else 0) : Nat) := by
          revert polys op hop;
          simp
          by_cases hℓ : ℓ = 0;
          · intro op hop polys;
            refine' ⟨ 0, _, Set.univ, _, _ ⟩ <;> aesop;
          · intro op hop polys;
            rcases AC₀_GateOps_cases hop with ( rfl | rfl | ⟨ n, rfl ⟩ );
            · refine' ⟨ 1, _, ∅, _, _ ⟩ <;> norm_num;
            · refine' ⟨ 1 - polys 0, _, ∅, _, _ ⟩ <;> norm_num;
              · refine' le_trans ( MvPolynomial.totalDegree_sub _ _ ) _ ; norm_num;
                exact le_mul_of_one_le_left ( Nat.zero_le _ ) ( by linarith [ Nat.pos_of_ne_zero hℓ ] );
              · intro x hx; specialize hx 0; aesop;
            · obtain ⟨ P, hP₁, hP₂ ⟩ := exists_good_approxAnd _ _ ℓ polys;
              refine' ⟨ P, hP₁, { x : Fin _ → Fin 2 | ¬ ( MvPolynomial.eval ( fun j => ( x j : ZMod 3 ) ) P ) = ∏ k : Fin n, ( MvPolynomial.eval ( fun j => ( x j : ZMod 3 ) ) ( polys k ) ) ^ 2 }, _, _ ⟩ <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
              · rw [ Finset.filter_not, Finset.card_sdiff ] at * ; norm_num at *;
                rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; norm_num at * ; linarith;
              · intro x hx₁ hx₂; rw [ Finset.prod_congr rfl fun i _ => by rw [ show ( MvPolynomial.eval ( fun j => ( x j : ZMod 3 ) ) ( polys i ) ) ^ 2 = if ( MvPolynomial.eval ( fun j => ( x j : ZMod 3 ) ) ( polys i ) ) = 1 then 1 else 0 from by rcases hx₂ i with h | h <;> simp +decide [ h ] ] ] ; simp +decide [ Finset.prod_ite ] ;
                cases h : Finset.card ( Finset.filter ( fun i => ¬ ( MvPolynomial.eval ( fun j => ( x j : ZMod 3 ) ) ( polys i ) ) = 1 ) Finset.univ ) <;> simp

lemma ncard_union_bound {α ι : Type*} [Finite ι] [Finite α] (S : ι → Set α) (B : ℚ)
    (h : ∀ i, (S i).ncard ≤ B) :
    (⋃ i, S i).ncard ≤ Nat.card ι * B := by
  have h_finite := Fintype.ofFinite ι;
  have h_finite : (Set.ncard (⋃ i, S i) : ℚ) ≤ ∑ i, (Set.ncard (S i) : ℚ) := by
    norm_cast;
    classical
    convert Finset.card_biUnion_le (t := fun i => Set.Finite.toFinset ( Set.toFinite ( S i ) ))
    · rw [ ← Set.ncard_coe_finset ] ; congr ; aesop;
    · exact Set.ncard_eq_toFinset_card _ (Set.toFinite _)
  exact h_finite.trans ( by simpa using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h i )

lemma exists_poly_approx_step {n ℓ : ℕ}
    (circ : FeedForward (Fin 2) (Fin n) (Fin 1))
    (h_finite : circ.finite)
    (h_gates : circ.onlyUsesGates AC₀_GateOps)
    (d : Fin circ.depth)
    (Polys_d : circ.nodes d.castSucc → MvPolynomial (Fin n) (ZMod 3))
    (BadSet_d : Set (Fin n → Fin 2))
    (h_deg : ∀ u, (Polys_d u).totalDegree ≤ (2 * ℓ) ^ (d : ℕ))
    (h_eval : ∀ x, x ∉ BadSet_d → ∀ u, ((circ.evalNode u x : Nat) : ZMod 3) = (Polys_d u).eval (fun j ↦ ((x j : Nat) : ZMod 3))) :
    ∃ (Polys_succ : circ.nodes d.succ → MvPolynomial (Fin n) (ZMod 3))
      (BadSet_succ : Set (Fin n → Fin 2)),
      (∀ u, (Polys_succ u).totalDegree ≤ (2 * ℓ) ^ (d.succ : ℕ)) ∧
      ((BadSet_succ.ncard : ℚ) ≤ (BadSet_d.ncard : ℚ) + (Nat.card (circ.nodes d.succ) : ℚ) * (2^n : ℚ) * (2 : ℚ)^(-ℓ : ℤ)) ∧
      (∀ x, x ∉ BadSet_succ → ∀ u, ((circ.evalNode u x : Nat) : ZMod 3) = (Polys_succ u).eval (fun j ↦ ((x j : Nat) : ZMod 3))) := by
  norm_num +zetaDelta at *;
  -- Apply `exists_poly_for_gate` to each node `u` in `circ.nodes d.succ`.
  have h_poly_for_gate : ∀ u : circ.nodes d.succ, ∃ P : MvPolynomial (Fin n) (ZMod 3), ∃ Bad : Set (Fin n → Fin 2),
    P.totalDegree ≤ 2 * ℓ * (⨆ i, (Polys_d (circ.gates d u |>.inputs i)).totalDegree) ∧
    (Bad.ncard : ℚ) ≤ (2 ^ n : ℚ) * (2 : ℚ) ^ (-ℓ : ℤ) ∧
    ∀ x : Fin n → Fin 2, x ∉ Bad →
      let inputs := fun i ↦ (Polys_d (circ.gates d u |>.inputs i) : MvPolynomial (Fin n) (ZMod 3)).eval (fun j ↦ ((x j : Nat) : ZMod 3))
      (∀ i, inputs i ∈ ({0, 1} : Set (ZMod 3))) →
      P.eval (fun j ↦ ((x j : Nat) : ZMod 3)) = (circ.gates d u |>.op.func (fun i ↦ if inputs i = 1 then 1 else 0) : Nat) := by
        intro u
        apply exists_poly_for_gate
        apply h_gates d u;
  choose P Bad hP hBad using h_poly_for_gate;
  refine' ⟨ P, _, BadSet_d ∪ ⋃ u, Bad u, _, _ ⟩;
  · intro u; specialize hP u; specialize hBad u; simp_all +decide [ pow_succ' ] ;
    refine' le_trans hP _;
    gcongr;
    exact ciSup_le' fun i ↦ h_deg ((circ.gates d u).inputs i);
  · refine' le_trans ( Nat.cast_le.mpr ( Set.ncard_union_le _ _ ) ) _;
    have h_union_bound : (⋃ u, Bad u).ncard ≤ (Nat.card (circ.nodes d.succ)) * (2 ^ n * (2 : ℚ) ^ (-ℓ : ℤ)) := by
      convert ncard_union_bound Bad _ _ using 1;
      · exact h_finite _;
      · exact fun u => hBad u |>.1;
    norm_num [ mul_assoc ] at * ; linarith;
  · intro x hx u;
    -- By definition of `evalNode`, we have:
    have h_evalNode : circ.evalNode u x = (circ.gates d u).op.func (fun i => circ.evalNode ((circ.gates d u).inputs i) x) := by
      exact rfl;
    simp_all +decide [ Set.mem_union, Set.mem_iUnion ];
    rw [ hBad u |>.2 x ( hx.2 u ) ];
    · congr! 2;
      congr! 2;
      specialize h_eval x hx.1 ( ( circ.gates d u ).inputs ‹_› );
      split_ifs <;> simp_all +decide [ ← h_eval ];
      · exact Fin.ext ( by erw [ ZMod.natCast_eq_natCast_iff ] at *; norm_num [ Nat.ModEq ] at *; omega );
      · exact Fin.ext ( by have := Fin.is_lt ( circ.evalNode ( ( circ.gates d u ).inputs ‹_› ) x ) ; interval_cases ( circ.evalNode ( ( circ.gates d u ).inputs ‹_› ) x : ℕ ) <;> trivial );
    · intro i; specialize h_eval x hx.1 ( circ.gates d u |>.inputs i ) ;
      rw [ ← h_eval ] ; have := Fin.exists_fin_two.mp ⟨ circ.evalNode ( circ.gates d u |>.inputs i ) x, rfl ⟩ ; aesop;

lemma exists_poly_approx_base {n ℓ : ℕ}
    (circ : FeedForward (Fin 2) (Fin n) (Fin 1)) :
    ∃ (Polys : circ.nodes 0 → MvPolynomial (Fin n) (ZMod 3))
      (BadSet : Set (Fin n → Fin 2)),
      (∀ u, (Polys u).totalDegree ≤ (2 * ℓ) ^ 0) ∧
      ((BadSet.ncard : ℚ) ≤ 0) ∧
      (∀ x, x ∉ BadSet → ∀ u, ((circ.evalNode u x : Nat) : ZMod 3) = (Polys u).eval (fun j ↦ ((x j : Nat) : ZMod 3))) := by
  use fun u => MvPolynomial.X (circ.nodes_zero ▸ u);
  use ∅;
  aesop

/-
For any layer i, there exist polynomials approximating the nodes at layer i, with degree at most (2ℓ)^i and total error set size proportional to the number of gates up to layer i.
-/
theorem exists_poly_approx_of_layer {n ℓ : ℕ}
    (circ : FeedForward (Fin 2) (Fin n) (Fin 1))
    (h_finite : circ.finite) (h_gates : circ.onlyUsesGates AC₀_GateOps)
    (i : Fin (circ.depth + 1)) :
    ∃ (Polys : circ.nodes i → MvPolynomial (Fin n) (ZMod 3))
      (BadSet : Set (Fin n → Fin 2)),
      (∀ u, (Polys u).totalDegree ≤ (2 * ℓ) ^ (i : ℕ)) ∧
      ((BadSet.ncard : ℚ) ≤ (∑ k : Fin i, Nat.card (circ.nodes ⟨k.1+1, by
        linarith [ Fin.is_lt i, Fin.is_lt k ]⟩)) * (2^n : ℚ) * (2 : ℚ)^(-ℓ : ℤ)) ∧
      (∀ x, x ∉ BadSet → ∀ u, ((circ.evalNode u x : Nat) : ZMod 3) = (Polys u).eval (fun j ↦ ((x j : Nat) : ZMod 3))) := by
  all_goals generalize_proofs at *;
  field_simp;
  induction i using Fin.inductionOn <;> simp_all +decide [ Fin.sum_univ_castSucc ];
  · refine' ⟨ _, _, _ ⟩;
    exact fun u => MvPolynomial.X ( cast circ.nodes_zero u );
    · exact fun u => by simp +decide [ MvPolynomial.totalDegree_X ] ;
    · refine' ⟨ ∅, _, _ ⟩ <;> aesop;
  · rename_i i hi;
    specialize hi fun k => by
      exact lt_of_lt_of_le k.2 ( Nat.le_of_lt ( Fin.is_lt _ ) )
    generalize_proofs at *;
    obtain ⟨ Polys, hPolys₁, x, hx₁, hx₂ ⟩ := hi;
    obtain ⟨ Polys', hPolys₁', x', hx₁', hx₂' ⟩ := exists_poly_approx_step circ h_finite h_gates _ Polys x hPolys₁ hx₂;
    refine' ⟨ Polys', _, hPolys₁', _, hx₂' ⟩ <;> norm_num [ pow_succ' ] at *;
    · assumption;
    · convert le_trans hx₁' ( add_le_add_right hx₁ _ ) using 1 ; ring!

end AristotleLemmas

/-- Applying this recursively, on an n-bit circuit of size s and depth h, we find a
polynomial with degree (2ℓ)^h and s2^(-ℓ) error rate. -/
theorem exists_good_poly_of_circuit (n ℓ : ℕ)
    (circ : FeedForward (Fin 2) (Fin n) (Fin 1))
    (h_finite : circ.finite) (h_gates : circ.onlyUsesGates AC₀_GateOps)  :
    ∃ (P : MvPolynomial (Fin n) (ZMod 3)),
      P.totalDegree ≤ (2 * ℓ) ^ circ.depth ∧
      { x | (circ.eval₁ x).val = P.eval (fun i ↦ (x i : ZMod 3))
      }.ncard ≥ (1 - circ.size * 2^(-ℓ : ℤ) : ℚ) * 2^n := by
  have h_error_bound : ∃ (Polys : circ.nodes (Fin.last circ.depth) → MvPolynomial (Fin n) (ZMod 3)) (BadSet : Set (Fin n → Fin 2)),
    (∀ u, (Polys u).totalDegree ≤ (2 * ℓ) ^ circ.depth) ∧
    ((BadSet.ncard : ℚ) ≤ circ.size * (2^n : ℚ) * (2 : ℚ)^(-ℓ : ℤ)) ∧
    (∀ x, x ∉ BadSet → ∀ u, ((circ.evalNode u x : Nat) : ZMod 3) = (Polys u).eval (fun j ↦ ((x j : Nat) : ZMod 3))) := by
      convert exists_poly_approx_of_layer circ h_finite h_gates ( Fin.last circ.depth ) using 1;
      rw [ show circ.size = ∑ k : Fin circ.depth, Nat.card ( circ.nodes ⟨ k.val + 1, by linarith [ Fin.is_lt k ] ⟩ ) from ?_ ];
      congr! 2;
      unfold FeedForward.size;
      convert Nat.card_sigma;
      exact fun a => h_finite _;
  obtain ⟨Polys, BadSet, hPolys, hBadSet, h_eval⟩ := h_error_bound;
  have h_card_eq : (Set.ncard {x : Fin n → Fin 2 | x ∈ BadSet}) + (Set.ncard {x : Fin n → Fin 2 | x ∉ BadSet}) = 2 ^ n := by
    rw [ ← Set.ncard_union_eq ];
    · rw [ show { x : Fin n → Fin 2 | x ∈ BadSet } ∪ { x : Fin n → Fin 2 | x∉BadSet } = Set.univ by ext; by_cases h : ( ‹_› : Fin n → Fin 2 ) ∈ BadSet <;> aesop, Set.ncard_univ ] ; norm_num;
    · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂ hx₁;
  have h_card_eq : (Set.ncard {x : Fin n → Fin 2 | x ∉ BadSet}) ≥ (2 ^ n : ℚ) - circ.size * (2 ^ n : ℚ) * (2 : ℚ) ^ (-ℓ : ℤ) := by
    simp_all
    rw [ ← @Nat.cast_inj ℚ ] at * ; push_cast at * ; linarith;
  refine' ⟨ Polys ( circ.nodes_last.symm.rec default ), hPolys _, _ ⟩;
  refine le_trans ?_ ( h_card_eq.trans ?_ );
  · ring_nf; norm_num;
  · gcongr with a
    · exact Set.toFinite _;
    · exact fun a_1 ↦ h_eval a a_1 _

/-
If a function grows polynomially, its logarithm grows logarithmically.
-/
lemma log_mem_log_of_mem_poly {f : ℕ → ℕ} (hf : f ∈ GrowthRate.poly) :
    (fun n ↦ Nat.log 2 (f n)) ∈ GrowthRate.log := by
  -- Since `log` is `O(ln)`, and `ln(f)` is `O(ln(n))`, we get that `log(f)` is `O(ln(n))`.
  have h_log_ln : (fun n => Real.log (f n)) =O[.atTop] (Real.log ·) := by
    -- Since `f` is poly, `f n ≤ C * n^k` for large `n`.
    obtain ⟨C, k, hk⟩ : ∃ C k : ℕ, ∀ᶠ n in .atTop, f n ≤ C * n ^ k := by
      obtain ⟨ C, hC ⟩ := hf;
      rw [ Asymptotics.isBigO_iff ] at hC;
      norm_num +zetaDelta at *;
      rcases hC with ⟨ c, a, hC ⟩ ; exact ⟨ ⌈c⌉₊, C, a, fun n hn => by exact_mod_cast hC n hn |> le_trans <| mul_le_mul_of_nonneg_right ( Nat.le_ceil _ ) <| by positivity ⟩ ;
    -- Then `log(f n) ≤ log(C * n^k) = log C + k * log n`.
    have h_log_bound : ∀ᶠ n in .atTop, Real.log (f n) ≤ Real.log C + k * Real.log n := by
      filter_upwards [ hk, Filter.eventually_gt_atTop 0 ] with n hn hn' ; rcases eq_or_ne ( f n ) 0 with h | h <;> simp_all
      · positivity;
      · have := Real.log_le_log ( by positivity ) ( show ( f n : ℝ ) ≤ C * n ^ k by exact_mod_cast hn );
        rw [ Real.log_mul ( by norm_cast; contrapose! h; aesop ) ( by positivity ), Real.log_pow ] at this ; linarith;
    -- Since $Real.log C$ and $k$ are constants, we can choose $M = Real.log C + k + 1$.
    have h_log_bound_const : ∃ M : ℝ, ∀ᶠ n in .atTop, Real.log (f n) ≤ M * Real.log n := by
      simp +zetaDelta at *;
      obtain ⟨ a, ha ⟩ := h_log_bound;
      refine' ⟨ ( Real.log C + k + 1 ) / Real.log 2, a + 2, fun b hb => le_trans ( ha b ( by linarith ) ) _ ⟩;
      rw [ div_mul_eq_mul_div, le_div_iff₀ ( Real.log_pos one_lt_two ) ];
      have := Real.log_two_lt_d9;
      nlinarith [ show ( 0 : ℝ ) ≤ Real.log C by positivity, show ( 0 : ℝ ) ≤ k * Real.log b by positivity, show ( 0 : ℝ ) ≤ Real.log b by exact Real.log_nonneg ( by norm_cast; linarith ), show ( Real.log b : ℝ ) ≥ Real.log 2 by exact Real.log_le_log ( by norm_num ) ( by norm_cast; linarith ) ];
    obtain ⟨ M, hM ⟩ := h_log_bound_const;
    rw [ Asymptotics.isBigO_iff ];
    exact ⟨ |M|, by filter_upwards [ hM, Filter.eventually_gt_atTop 1 ] with n hn hn'; rw [ Real.norm_of_nonneg ( Real.log_natCast_nonneg _ ), Real.norm_of_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr hn'.le ) ) ] ; cases abs_cases M <;> nlinarith [ Real.log_nonneg ( Nat.one_le_cast.mpr hn'.le ) ] ⟩;
  convert h_log_ln using 1;
  constructor <;> intro h;
  · exact h_log_ln;
  · -- Since $\log_2(f(n)) = \frac{\ln(f(n))}{\ln(2)}$, and $\ln(f(n)) = O(\ln(n))$, it follows that $\log_2(f(n)) = O(\ln(n))$.
    rw [GrowthRate.log_iff_rlog]
    have h_log2_ln : ∀ n, (Nat.log 2 (f n)) ≤ Real.log (f n) / Real.log 2 := by
      intro n
      rw [ le_div_iff₀ ( Real.log_pos one_lt_two ) ]
      rw [ ← Real.log_pow ]
      rcases eq_or_ne ( f n ) 0 with h | h <;> simp_all
      rw [ ← Real.log_rpow zero_lt_two ]
      exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self 2 h )
    refine' Asymptotics.IsBigO.trans _ h;
    refine' Asymptotics.IsBigO.of_bound ( 1 / Real.log 2 ) _;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ), Real.norm_of_nonneg ( Real.log_natCast_nonneg _ ) ] ; convert h_log2_ln n using 1 ; ring;

/--
If a function `size` grows polynomially, there exists a logarithmic parameter
`ℓ` such that `2^ℓ` dominates `3 * size`.
-/
lemma exists_log_param_of_poly_size {size : ℕ → ℕ} (h_size : size ∈ GrowthRate.poly) :
    ∃ (ℓ : ℕ → ℕ),
      (ℓ ∈ GrowthRate.log) ∧
      (∀ n, 3 * size n ≤ 2^(ℓ n)) := by
  -- Since `3 * size n` grows polynomially, we can apply `log_mem_log_of_mem_poly` to show that `fun n ↦ Nat.log 2 (3 * size n)` is in `GrowthRate.log`.
  have h_log : (fun n ↦ Nat.log 2 (3 * size n)) ∈ GrowthRate.log := by
    apply log_mem_log_of_mem_poly;
    obtain ⟨ C, hC ⟩ := h_size;
    use C;
    norm_num +zetaDelta at *;
    exact Asymptotics.IsBigO.const_mul_left hC 3;
  -- Define `ℓ n := Nat.log 2 (3 * size n) + 1`.
  use fun n => Nat.log 2 (3 * size n) + 1;
  -- Show that ℓ is in GrowthRate.log.
  apply And.intro;
  · apply_rules [ GrowthRate.LawfulGrowthRate.mem_add ];
    -- The constant function 1 is in GrowthRate.log because it is bounded by a constant.
    have h_const : (fun n => 1 : ℕ → ℕ) ∈ GrowthRate.const := by
      exact Asymptotics.isBigO_refl _ _;
    exact GrowthRate.const_subset_log h_const;
  · exact fun n => Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ )

/--
If `ℓ` is logarithmic, then `(2 * ℓ)^d` is polylogarithmic for any constant `d`.
-/
lemma polylog_of_log_pow_const {ℓ : ℕ → ℕ} (hℓ : ℓ ∈ GrowthRate.log) (d : ℕ) :
    (fun n ↦ (2 * ℓ n) ^ d) ∈ GrowthRate.polylog := by
  have h_mul : (fun n ↦ 2 * ℓ n) ∈ GrowthRate.log := by
    unfold GrowthRate.log at *;
    unfold GrowthRate.bigO at *;
    simpa [ Asymptotics.IsBigO ] using hℓ.const_mul_left 2;
  exact ⟨ d, by simpa using h_mul.pow d ⟩

theorem AC₀_low_degree : ∀ F ∈ AC₀, ∃ (P : (n : ℕ) → MvPolynomial (Fin n) (ZMod 3)),
    --The degree is polylog(n)
    (MvPolynomial.totalDegree <| P · : ℕ → ℕ) ∈ GrowthRate.polylog
    ∧
    ( ∀ n, --The polynomial agrees on at least 2/3rd of inputs
      { x | (F n x).val = (P n).eval (fun i ↦ (x i : ZMod 3))
      }.ncard ≥ (2/3 : ℚ) * 2^n
    )
    := by
  intros F hF
  obtain ⟨CF, hCF⟩ := hF;
  -- Let `size n = (CF n).size` and `depth n = (CF n).depth`.
  set size : ℕ → ℕ := fun n => (CF n).size
  set depth : ℕ → ℕ := fun n => (CF n).depth;
  -- Since `depth ∈ const`, there exists `D` such that `∀ n, depth n ≤ D`.
  obtain ⟨D, hD⟩ : ∃ D, ∀ n, depth n ≤ D := by
    have := hCF.2.2.1;
    exact GrowthRate.bounded_of_const this;
  -- Since `size ∈ poly`, by `exists_log_param_of_poly_size`, there exists `ℓ₀ ∈ log` such that `3 * size n ≤ 2^(ℓ₀ n)`.
  obtain ⟨ℓ₀, hℓ₀_log, hℓ₀⟩ : ∃ ℓ₀ : ℕ → ℕ, (ℓ₀ ∈ GrowthRate.log) ∧ (∀ n, 3 * size n ≤ 2^(ℓ₀ n)) := by
    have := hCF.2.1.2;
    exact exists_log_param_of_poly_size this;
  -- Let `ℓ n := ℓ₀ n + 1`. Then `ℓ ∈ log` and `2 * ℓ n ≥ 2`.
  set ℓ : ℕ → ℕ := fun n => ℓ₀ n + 1
  have hℓ_log : ℓ ∈ GrowthRate.log := by
    have hℓ_log : (fun n => ℓ₀ n + 1) ∈ GrowthRate.log := by
      have hℓ₀_log : ℓ₀ ∈ GrowthRate.log := hℓ₀_log
      have hℓ_log : (fun n => ℓ₀ n + 1) ∈ GrowthRate.log := by
        have h_log_add : ∀ {f g : ℕ → ℕ}, f ∈ GrowthRate.log → g ∈ GrowthRate.const → (fun n => f n + g n) ∈ GrowthRate.log := by
          intros f g hf hg;
          have h_log_add : (fun n => f n + g n) ∈ GrowthRate.log := by
            have h_log_add : (fun n => f n) ∈ GrowthRate.log := hf
            have h_log_add : (fun n => g n) ∈ GrowthRate.const := hg
            apply_rules [ GrowthRate.LawfulGrowthRate.mem_add ];
            exact GrowthRate.const_subset_log h_log_add;
          exact h_log_add
        exact h_log_add hℓ₀_log ( show ( fun n => 1 ) ∈ GrowthRate.const from by exact Set.mem_setOf.mpr <| by exact Asymptotics.isBigO_refl _ _ )
      exact hℓ_log;
    exact hℓ_log
  have hℓ_ge_two : ∀ n, 2 * ℓ n ≥ 2 := by
    grind +ring;
  -- Apply `exists_good_poly_of_circuit` with `ℓ n` to get `P n`.
  obtain ⟨P, hP⟩ : ∃ P : (n : ℕ) → MvPolynomial (Fin n) (ZMod 3), (∀ n, (P n).totalDegree ≤ (2 * ℓ n) ^ D) ∧ (∀ n, {x : Fin n → Fin 2 | (F n x).val = (MvPolynomial.eval (fun i => (x i : ZMod 3)) (P n))}.ncard ≥ (1 - size n * 2^(-ℓ n : ℤ) : ℚ) * 2^n) := by
    have h_exists_poly : ∀ n, ∃ P : MvPolynomial (Fin n) (ZMod 3), (P.totalDegree ≤ (2 * ℓ n) ^ D) ∧ ({x : Fin n → Fin 2 | (F n x).val = (MvPolynomial.eval (fun i => (x i : ZMod 3)) P)}.ncard ≥ (1 - size n * 2^(-ℓ n : ℤ) : ℚ) * 2^n) := by
      intro n
      obtain ⟨P, hP⟩ := exists_good_poly_of_circuit n (ℓ n) (CF n) (hCF.2.1.1 n) (hCF.2.2.2 n);
      exact ⟨ P, le_trans hP.1 ( pow_le_pow_right₀ ( by linarith [ hℓ_ge_two n ] ) ( hD n ) ), by simpa only [ hCF.1 n ] using hP.2 ⟩;
    exact ⟨ fun n => Classical.choose ( h_exists_poly n ), fun n => Classical.choose_spec ( h_exists_poly n ) |>.1, fun n => Classical.choose_spec ( h_exists_poly n ) |>.2 ⟩;
  -- Since `polylog` is lawful, the degree of `P` is in `polylog`.
  have hP_polylog : (fun n => (P n).totalDegree) ∈ GrowthRate.polylog := by
    have hP_polylog : (fun n => (2 * ℓ n) ^ D) ∈ GrowthRate.polylog := by
      exact polylog_of_log_pow_const hℓ_log D;
    obtain ⟨ C, hC ⟩ := hP_polylog;
    refine' ⟨ C, _ ⟩;
    rw [ Asymptotics.isBigO_iff ] at *;
    norm_num +zetaDelta at *;
    obtain ⟨ c, a, hc ⟩ := hC;
    use c, a + 1;
    intro n hn; specialize hc n ( by linarith ) ; norm_num [ Norm.norm ] at *;
    exact le_trans ( mod_cast hP.1 n ) ( mod_cast hc );
  refine' ⟨ P, hP_polylog, fun n => le_trans _ ( hP.2 n ) ⟩;
  norm_num [ zpow_add₀, zpow_neg ];
  field_simp;
  norm_cast;
  rw [ Int.subNatNat_eq_coe ] ; push_cast ; linarith [ hℓ₀ n, pow_succ' 2 ( ℓ₀ n ) ]

/-- We'll show that parity cannot be computed by a low-degree polymomial mod 3. First,
if we had a low-degree polynomial that computed parity on bits, then this yields a
polynomial of equal degree that computes the products on {-1, 1} (at exactly as many
places as we compute parity correctly). -/
theorem parity_implies_product_mod3 (n : ℕ) (P : MvPolynomial (Fin n) (ZMod 3)) :
    ∃ Q : MvPolynomial (Fin n) (ZMod 3),
      Q.totalDegree = P.totalDegree ∧
      ∀ x : Fin n → Fin 2,
        P.eval (fun i ↦ (x i : ZMod 3)) = ∑ i, x i
        ↔
        Q.eval (fun i ↦ (2 * (x i).val - 1 : ZMod 3)) = ∏ i, (2 * (x i).val - 1 : ZMod 3)
       := by
  -- use P(x₁ - 1, x₂ - 1, ... ) + 1
  sorry

/-- The parity function is not well approximated by low-degree polynomials in 𝔽₃. -/
theorem parity_not_low_degree : ¬∃ (P : (n : ℕ) → MvPolynomial (Fin n) (ZMod 3)),
    --The degree is polylog(n)
    (MvPolynomial.totalDegree <| P · : ℕ → ℕ) ∈ GrowthRate.polylog
    ∧
    ( ∀ n, --The polynomial agrees on at least 2/3rd of inputs
      { x | (FuncFamily.PARITY n x).val = (P n).eval (fun i ↦ (x i : ZMod 3))
      }.ncard ≥ (2/3 : ℚ) * 2^n
    )
    := by
  --Theorem 6 in https://homes.cs.washington.edu/~anuprao/pubs/CSE531Winter12/lecture10.pdf
  sorry

/-- AC₀ cannot compute parity: it is too sensitive. -/
theorem AC₀_not_parity : FuncFamily.PARITY ∉ AC₀ := by
  by_contra h
  replace h := AC₀_low_degree _ h
  exact parity_not_low_degree h
