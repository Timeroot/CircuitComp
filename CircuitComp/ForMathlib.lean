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

lemma sum_choose_half_le (n : ℕ) :
    ∑ i ∈ Finset.range (n / 2 + 1), n.choose i ≤ 2 ^ (n - 1) + n.choose (n / 2) := by
  suffices ∑ i ∈ Finset.range (n / 2 + 1), (n.choose i : ℝ) ≤ 2^(n - 1) + n.choose (n / 2) by
    exact_mod_cast this
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
  · norm_cast;
    -- Let's simplify the sum $\sum_{i=0}^{k} \binom{2k}{i}$.
    have h_sum : ∑ i ∈ Finset.range (k + 1), (Nat.choose (2 * k) i : ℝ) = (2 ^ (2 * k) + (Nat.choose (2 * k) k : ℝ)) / 2 := by
      have h_split : ∑ i ∈ Finset.range (k + 1), (Nat.choose (2 * k) i : ℝ) + ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (Nat.choose (2 * k) i : ℝ) = 2 ^ (2 * k) := by
        rw_mod_cast [ Finset.sum_range_add_sum_Ico _ ( by linarith ) ];
        rw [ Nat.sum_range_choose ];
      -- By symmetry of binomial coefficients, we have $\sum_{i=k+1}^{2k} \binom{2k}{i} = \sum_{i=0}^{k-1} \binom{2k}{i}$.
      have h_symm : ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), (Nat.choose (2 * k) i : ℝ) = ∑ i ∈ Finset.range k, (Nat.choose (2 * k) i : ℝ) := by
        rw [ Finset.sum_Ico_eq_sum_range ];
        norm_num [ two_mul, add_assoc ];
        rw [ ← Finset.sum_range_reflect ];
        exact Finset.sum_congr rfl fun x hx => by
          rw [ Nat.choose_symm_of_eq_add ]
          linarith [ Nat.sub_add_cancel ( show 1 ≤ k from Nat.pos_of_ne_zero ( by aesop ) ), Nat.sub_add_cancel ( show x ≤ k - 1 from Nat.le_sub_one_of_lt ( Finset.mem_range.mp hx ) ) ] ;
      norm_num [ Finset.sum_range_succ ] at * ; linarith;
    rcases k with ( _ | k ) <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
    rw [ ← @Nat.cast_le ℝ ] ; push_cast ; linarith [ show ( Nat.choose ( 2 * k + 2 ) ( k + 1 ) : ℝ ) ≥ 0 by positivity ];
  · -- By symmetry of binomial coefficients, we have $\sum_{i=0}^{k} \binom{2k+1}{i} = \sum_{i=k+1}^{2k+1} \binom{2k+1}{i}$.
    have h_symm : ∑ i ∈ Finset.range (k + 1), (Nat.choose (2 * k + 1) i : ℝ) = ∑ i ∈ Finset.Ico (k + 1) (2 * k + 2), (Nat.choose (2 * k + 1) i : ℝ) := by
      rw [ Finset.sum_Ico_eq_sum_range ];
      rw [ show 2 * k + 2 - ( k + 1 ) = k + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; rw [ ← Finset.sum_flip ] ; simp +arith [ two_mul, add_assoc ];
      exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hx ) ] ;
    -- Adding these two sums, we get the sum of all binomial coefficients of $2k+1$, which is $2^{2k+1}$.
    have h_sum : ∑ i ∈ Finset.range (k + 1), (Nat.choose (2 * k + 1) i : ℝ) + ∑ i ∈ Finset.Ico (k + 1) (2 * k + 2), (Nat.choose (2 * k + 1) i : ℝ) = 2 ^ (2 * k + 1) := by
      rw [ Finset.sum_range_add_sum_Ico _ ( by linarith ) ] ; norm_cast ; simp +arith [ Nat.sum_range_choose ] ;
    norm_num [ Nat.add_div ] at *;
    norm_num [ pow_succ' ] at * ; linarith [ show ( Nat.choose ( 2 * k + 1 ) k : ℝ ) ≥ 0 by positivity ]

lemma central_binom_le {n : ℕ} (hn : 0 < n) : (2 * n).choose n ≤ 2 ^ (2 * n) / Real.sqrt (2 * n + 1) := by
  rw [ le_div_iff₀ ]
  · -- Squaring both sides to remove the square root.
    suffices h_sq : (Nat.choose (2 * n) n : ℝ) ^ 2 * (2 * n + 1) ≤ 4 ^ (2 * n) by
      contrapose! h_sq;
      convert pow_lt_pow_left₀ h_sq ( by positivity ) two_ne_zero using 1
      · ring_nf
        norm_num [ pow_mul' ];
      · ring_nf
        rw [ Real.sq_sqrt ] <;> linarith;
    induction hn <;> norm_num [ Nat.cast_choose, Nat.mul_succ, pow_succ', pow_mul' ] at *;
    rw [ Nat.cast_choose ] at * <;> try linarith;
    simp_all [ two_mul, add_assoc, Nat.factorial ];
    norm_num [ Nat.add_sub_add_left, Nat.factorial_succ ] at *;
    field_simp at *;
    nlinarith [ ( by positivity : 0 ≤ ( ( ‹ℕ› : ℕ ) : ℝ ) ^ 3 ), ( by positivity : 0 ≤ ( ( ‹ℕ› : ℕ ) : ℝ ) ^ 2 ), ( by positivity : 0 ≤ ( ( ‹ℕ› : ℕ ) : ℝ ) ), ( by positivity : 0 ≤ ( ( ‹ℕ› : ℕ ) : ℝ ) ^ 4 ) ];
  · positivity;

lemma choose_self_div_two {n : ℕ} (hn : 0 < n) : n.choose (n / 2) ≤ 2 ^ n / Real.sqrt n := by
  -- We'll use the fact that the central binomial coefficient is bounded by $\frac{2^n}{\sqrt{n}}$. This follows from the properties of binomial coefficients.
  rcases n.even_or_odd' with ⟨ k, rfl | rfl ⟩
  · norm_num at *
    grw [central_binom_le hn]
    rw [ ← Real.sqrt_mul ( by norm_num ) ]
    exact div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( Real.sqrt_le_sqrt <| by norm_cast; linarith )
  · have := central_binom_le (n := k + 1 ) ; norm_num [ Nat.add_div ] at *;
    rw [ le_div_iff₀ ] at * <;> norm_num [ Nat.cast_choose, Nat.mul_succ, pow_succ' ] at *;
    · rw [ show ( 2 * k + 2 ).choose ( k + 1 ) = ( 2 * k + 1 ).choose k + ( 2 * k + 1 ).choose ( k + 1 ) by rw [ Nat.choose_succ_succ ] ] at this ; norm_num [ Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow ] at *;
      nlinarith [ Real.sqrt_nonneg ( 2 * ( k + 1 ) + 1 ), Real.sqrt_le_sqrt ( by linarith : ( 2 * k + 1 : ℝ ) ≤ 2 * ( k + 1 ) + 1 ), Real.mul_self_sqrt ( by linarith : ( 0 : ℝ ) ≤ 2 * ( k + 1 ) + 1 ), Real.mul_self_sqrt ( by linarith : ( 0 : ℝ ) ≤ 2 * k + 1 ), show ( Nat.choose ( 2 * k + 1 ) ( k + 1 ) : ℝ ) = Nat.choose ( 2 * k + 1 ) k from mod_cast Nat.choose_symm_of_eq_add <| by linarith ];
    · positivity;
    · positivity;

lemma isBigO_choose_half_div_two_pow :
    (fun n : ℕ ↦ (n.choose (n / 2) : ℝ)) =O[.atTop] (fun n ↦ (2 : ℝ)^n / Real.sqrt n) := by
  simp_rw [Asymptotics.isBigO_iff, Filter.eventually_atTop]
  use 1, 1
  conv in _ ≤ _ => rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  exact @choose_self_div_two

lemma exists_constant_degree_bound :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n ≥ N, ∀ k : ℕ,
      (∑ i ∈ Finset.range (n / 2 + k + 1), (n.choose i : ℝ)) ≥ (2/3 : ℝ) * 2^n →
      (k : ℝ) ≥ c * Real.sqrt n := by
  -- By definition of big O notation, there exists a constant C such that for all sufficiently large n, binom(n, n/2) ≤ C * 2^n / sqrt(n).
  obtain ⟨C, hC⟩ : ∃ C > 0, ∀ᶠ n in Filter.atTop, (Nat.choose n (n / 2) : ℝ) ≤ C * 2^n / Real.sqrt n := by
    have := isBigO_choose_half_div_two_pow;
    rw [ Asymptotics.isBigO_iff' ] at this;
    exact ⟨ this.choose, this.choose_spec.1, by simpa [ mul_div_assoc, abs_of_nonneg, Real.sqrt_nonneg ] using this.choose_spec.2 ⟩;
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( hC.2 );
  -- Let's choose $c = \frac{1}{7C}$.
  use 1 / (7 * C);
  refine' ⟨ N + 42 ^ 2 * ⌈C ^ 2⌉₊ + 1, by exact one_div_pos.mpr <| mul_pos ( by norm_num ) hC.1, fun n hn k hk => _ ⟩;
  -- By `sum_choose_le_half_plus_k_times_central`, $\sum \le 2^{n-1} + (k+1) \binom{n}{n/2}$.
  have h_sum_le : (∑ i ∈ Finset.range (n / 2 + k + 1), (Nat.choose n i : ℝ)) ≤ 2^(n-1) + (k + 1) * (Nat.choose n (n / 2) : ℝ) := by
    have h_sum_split : (∑ i ∈ Finset.range (n / 2 + k + 1), (Nat.choose n i : ℝ)) ≤ (∑ i ∈ Finset.range (n / 2 + 1), (Nat.choose n i : ℝ)) + (k * (Nat.choose n (n / 2) : ℝ)) := by
      have h_sum_split : (∑ i ∈ Finset.Ico (n / 2 + 1) (n / 2 + k + 1), (Nat.choose n i : ℝ)) ≤ (k : ℝ) * (Nat.choose n (n / 2) : ℝ) := by
        have h_sum_split : ∀ i ∈ Finset.Ico (n / 2 + 1) (n / 2 + k + 1), (Nat.choose n i : ℝ) ≤ (Nat.choose n (n / 2) : ℝ) := by
          intros i hi;
          norm_cast;
          convert Nat.choose_le_middle _ _;
        simpa [ add_assoc ] using Finset.sum_le_sum h_sum_split;
      rw [ ← Finset.sum_range_add_sum_Ico _ ( by linarith : n / 2 + 1 ≤ n / 2 + k + 1 ) ] ; linarith
    have h_sum : ∑ i ∈ Finset.range (n / 2 + 1), (n.choose i : ℝ) ≤ 2^(n-1) + n.choose (n / 2) :=
      mod_cast sum_choose_half_le n
    linarith
  -- Substitute the bound for $\binom{n}{n/2}$ into the inequality.
  have h_subst : (k + 1) * (C * 2^n / Real.sqrt n) ≥ 2^n / 6 := by
    specialize hN n ( by linarith )
    rcases n <;> norm_num [ pow_succ' ] at * ; nlinarith;
  -- Simplify the inequality $(k + 1) * (C * 2^n / \sqrt{n}) \geq 2^n / 6$ to get $k + 1 \geq \sqrt{n} / (6C)$.
  have h_simplified : (k + 1 : ℝ) ≥ Real.sqrt n / (6 * C) := by
    rw [ ge_iff_le, div_le_iff₀ ] <;> nlinarith [ show 0 < C * 2 ^ n / Real.sqrt n by exact div_pos ( mul_pos hC.1 ( pow_pos zero_lt_two _ ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ) ), show 0 < ( 2 : ℝ ) ^ n by positivity, mul_div_cancel₀ ( C * 2 ^ n ) ( ne_of_gt ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ) ) ) ];
  ring_nf at *;
  nlinarith [ show ( n : ℝ ) ≥ 1 + N + ⌈C ^ 2⌉₊ * 1764 by exact_mod_cast hn, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, inv_pos.mpr hC.1, mul_inv_cancel₀ hC.1.ne', Nat.le_ceil ( C ^ 2 ), pow_two_nonneg ( C - 1 ), pow_two_nonneg ( C + 1 ) ]
