import CircuitComp.Basic
import CircuitComp.NC

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees

open FeedForward
open CircuitFamily

def AC₀_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Unit, fun x ↦ 1 - x ()⟩} --NOT
  ∪
  ⋃ n, {⟨Fin n, fun x ↦ ∏ i, x i⟩} --ANDs of all arity

/-- AC₀, the constant-depth polynomial-size circuits of NOT gates and arbitrary-arity AND gates. -/
def AC₀ : Set (FuncFamily (Fin 2)) :=
  CircuitClass .poly .const AC₀_GateOps

/-- The class NC₀ is contained in AC₀. -/
theorem NC₀_subset_AC₀ : NC₀ ⊆ AC₀ := by
  apply CircuitClass.Monotone_gates
  intro g
  rw [NC₀_GateOps, AC₀_GateOps]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.iUnion_singleton_eq_range,
    Set.singleton_union, Set.mem_range]
  rintro (rfl|rfl)
  · simp
  · right
    use 2
    simp_rw [Fin.prod_univ_two]

/-- The AND problem is contained in AC₀, because we can take a single AND gate. -/
theorem AND_mem_AC₀ : and_family ∈ AC₀ := by
  use (fun n ↦ ⟨
    1,
    ![Fin n, Unit],
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
    simp only [Fin.isValue, Fin.castSucc_zero, Matrix.cons_val_zero, id_eq, eq_mpr_eq_cast,
      Fin.reduceLast, Matrix.cons_val_one, Nat.reduceAdd]
    intro i
    fin_cases i <;> simp <;> infer_instance
  · simp [size]
    use 0
    simp only [Nat.cast_one, pow_zero, Asymptotics.isBigO_const_const_iff, imp_self]
  · simp only [hasDepth, GrowthRate.const, GrowthRate.bigO, Pi.one_apply, Nat.cast_one,
      Set.mem_setOf_eq, Asymptotics.isBigO_const_const_iff, one_ne_zero, imp_self]
  · simp only [CircuitFamily.onlyUsesGates, FeedForward.onlyUsesGates]
    intro n d _
    simp only [AC₀_GateOps, Fin.isValue, Set.iUnion_singleton_eq_range, Set.singleton_union,
      Set.mem_insert_iff, GateOp.mk.injEq, Set.mem_range]
    right
    use n

theorem NC₀_ssubset_AC₀ : NC₀ ⊂ AC₀ := by
  refine ssubset_of_ne_of_subset ?_ NC₀_subset_AC₀
  intro h
  apply AND_not_mem_NC₀
  rw [h]
  exact AND_mem_AC₀

/-- The problem PARITY: Compute the parity of the input bits. -/
def parity_family : FuncFamily (Fin 2) :=
  fun _ xs ↦ ∑ i, xs i

/-- Functions in AC₀ are well approximated by a low-degree polynomial in 𝔽₃. -/
theorem AC₀_low_degree : ∀ F ∈ AC₀, ∃ (P : (n : ℕ) → MvPolynomial (Fin n) (Fin 3)),
    --The degree is polylog(n)
    (MvPolynomial.totalDegree <| P · : ℕ → ℕ) ∈ GrowthRate.polylog
    ∧
    ( ∀ n, --The polynomial agrees on at least 2/3rd of inputs
      { x | (F n x).val = (P n).eval (fun i ↦ ⟨x i, Nat.lt_succ_of_lt (x i).2⟩)
      }.ncard ≥ (2/3 : ℚ) * 2^n
    )
    := by
  --Induction on depth
  --If the final gate is a NOT: use 1-P
  --If the final gate is an AND: use 1 - Π_{k=ℓ} (1 - (∑_{i∈Sₖ} P_i)^2 ) where we pick ℓ random
  -- sets Sₖ. See https://homes.cs.washington.edu/~anuprao/pubs/CSE531Winter12/lecture10.pdf
  sorry

/-- The parity function is not well approximated by low-degree polynomials in 𝔽₃. -/
theorem parity_not_low_degree : ¬∃ (P : (n : ℕ) → MvPolynomial (Fin n) (Fin 3)),
    --The degree is polylog(n)
    (MvPolynomial.totalDegree <| P · : ℕ → ℕ) ∈ GrowthRate.polylog
    ∧
    ( ∀ n, --The polynomial agrees on at least 2/3rd of inputs
      { x | (parity_family n x).val = (P n).eval (fun i ↦ ⟨x i, Nat.lt_succ_of_lt (x i).2⟩)
      }.ncard ≥ (2/3 : ℚ) * 2^n
    )
    := by
  --Theorem 6 in https://homes.cs.washington.edu/~anuprao/pubs/CSE531Winter12/lecture10.pdf
  sorry

/-- AC₀ cannot compute parity: it is too sensitive. -/
theorem AC₀_not_parity : parity_family ∉ AC₀ := by
  by_contra h
  replace h := AC₀_low_degree _ h
  exact parity_not_low_degree h
