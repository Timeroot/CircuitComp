import CircuitComp.Circuit
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Nat.Log

open FeedForward
open CircuitFamily

/-- A fairly minimal set of gates for NC classes: just NOT and AND. Technically, we should also take the
identity gate (for forwarding operations between layers) and a constant gate (for the 0-ary case). -/
def NC_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Fin 0, 1⟩, --Constant one gate
   ⟨Fin 1, (· 0)⟩, --Id
   ⟨Fin 1, fun x ↦ 1 - x 0⟩, --NOT
  ⟨Fin 2, fun x ↦ x 0 * x 1⟩} --AND

--TODO: We can drop Id (by using `x AND x`) with no penalty to depth or size.
-- We can drop constant gates (by inlining) as long as the input is a nonempty type,
-- but the empty type case is a pain and why we include constant gates. Showing that *adding* gates
-- doesn't change the class is a separate question, see proof_wanted `NCi_other_gates` below.

/-- The circuit class of nonuniform NC⁰: constant depth polynomial-size circuits with
fanin-2 NOTs and ANDs. -/
def NC₀ : Set (FuncFamily₁ (Fin 2)) :=
  CircuitClass .poly .const NC_GateOps

/-- The circuit class of nonuniform NCi: polynomial-size circuits with
NOTs and fanin-2 ANDs, and depth O(logⁱ n). -/
def NCi (i : ℕ) : Set (FuncFamily₁ (Fin 2)) :=
  CircuitClass .poly (.bigO (Nat.log2 · ^ i)) NC_GateOps

/-- NC₀ is the 0th element of the NCi hierarchy -/
theorem NCi_zero : NCi 0 = NC₀ := by
  rfl --Wait, this actually holds by definitional equality? That's hilarious

def NC : Set (FuncFamily₁ (Fin 2)) :=
  ⋃ i, NCi i

theorem NCi_subset_NC (i : ℕ) : NCi i ⊆ NC :=
  Set.subset_iUnion_of_subset i fun _ ↦ id

/-- All gates in `NC_GateOps` have fan-in at most 2. -/
lemma NC₀_fanin_le_2 : ∀ op ∈ NC_GateOps, Finite op.ι ∧ Nat.card op.ι ≤ 2 := by
  unfold NC_GateOps
  aesop (add safe Finite.of_fintype)

/-- Any function family in NC₀ has a bounded arity (more precisely, a bounded size `EssDomain`). -/
theorem bounded_essDomain_of_mem_NC₀ {fn : FuncFamily₁ (Fin 2)} (h : fn ∈ NC₀) :
    ∃ k, ∀ n, (fn n).EssDomain.ncard ≤ k := by
  rw [NC₀, mem_circuitClass_iff Unit] at h
  obtain ⟨CF, hCF₁, hCF₂, hCF₃, hCF₄, hCF₅⟩ := h
  obtain ⟨C, hC⟩ := GrowthRate.bounded_of_const hCF₄
  use 2 ^ C
  intro n
  have h_essDomain_subset_inputDeps : (fn n).EssDomain ⊆ (CF n).inputDeps
      (Fin.last (CF n).depth) (CF n |> FeedForward.nodes_last |> fun h => h.symm.rec default) := by
    rw [← hCF₂ n]
    unfold FeedForward.eval₁
    convert FeedForward.essDomain_subset_inputDeps _
  apply (Set.ncard_le_ncard h_essDomain_subset_inputDeps).trans
  refine ((CF n).inputDeps_card_le _ 2 ?_).trans ?_
  · exact fun d n_2 ↦ NC₀_fanin_le_2 ((CF n).gates d n_2).op (hCF₅ n d n_2);
  · exact pow_le_pow_right₀ one_le_two (hC n)

/-- The AND problem is not in the class NC₀, because NC₀ only has functions
of bounded support, and AND is arbitrarilty large support. -/
theorem AND_not_mem_NC₀ : FuncFamily₁.AND ∉ NC₀ := by
  intro h
  obtain ⟨k, hk⟩ := bounded_essDomain_of_mem_NC₀ h
  specialize hk (k+1)
  rw [FuncFamily₁.AND_EssDomain] at hk
  simp [Set.ncard_univ] at hk

/-- The definition of NCi is unchanged if you add any larger *finite* set of
  *finite arity* gates. -/
proof_wanted NCi_other_gates {i : ℕ} {S : Set (GateOp (Fin 2))} [Finite S] (hS : NC_GateOps ⊆ S)
    (hS₂ : ∀ s ∈ S, Finite s.ι) :
    NCi i = CircuitClass .poly (.bigO (Nat.log2 · ^ i)) S

/-- Constructing the NC1 AND circuit for n > 0, with an output type of `Fin 1` for mathematical
uniformity in the construction. -/
def NC1_AND_CircuitFamily : CircuitFamily₁ (Fin 2) (Fin 1) := fun n ↦
  if hn : n = 0 then --The 0-bit input case
   ⟨1, --depth 1
    fun i ↦ Fin i.val, --width 1 on its only layer. width 0 at input.
    fun _ _ ↦ ⟨⟨Fin 0, 1⟩, Fin.elim0⟩, -- a single constant "1" gate
    let _ := hn; by subst n; rfl,
    let _ := hn; by simp⟩
  else
   ⟨Nat.clog 2 n, --depth
    --the width at layer k is n/2^k, at the last layer this means we're `Fin 1`.
    fun k ↦ Fin ⌈n / (2^k.val : ℚ)⌉₊,
    fun d x ↦
      if hx : x.val + 1 = ⌈(n / 2 ^ d.succ.val : ℚ)⌉₊ ∧ ⌈(n / 2 ^ d.val : ℚ)⌉₊ % 2 = 1 then
        --Well, if x is the last one in its layer and the parent layer is odd,
        --then we just use an identity gate.
        ⟨⟨Fin 1, (· 0)⟩, fun _ ↦ ⟨2 * x.val,
          let _ := hn; let _ := hx; by
          rw [Nat.lt_ceil, Nat.cast_mul]
          convert mul_lt_mul_of_pos_left (Nat.lt_ceil.mp x.is_lt) zero_lt_two using 1
          rw [Fin.val_succ, Fin.coe_castSucc]
          ring
        ⟩⟩
      else --otherwise we take the AND
        ⟨⟨Fin 2, fun x ↦ x 0 * x 1⟩, fun (i : Fin 2) ↦ ⟨2 * x.val + i,
          let _ := hn; let hx2 := hx; by
          clear hx2
          simp only [Fin.val_succ, Fin.coe_castSucc] at ⊢
          have hx_lt := x.2
          simp only [Fin.val_succ, pow_succ, ← div_div] at hx_lt
          fin_cases i
          · rw [ Nat.lt_ceil ] at *
            simp
            linarith
          · norm_num [ pow_succ, ← div_div ] at *
            rw [ Nat.lt_ceil ] at *;
            norm_num +zetaDelta at *;
            contrapose! hx;
            refine' ⟨ _, _ ⟩;
            · symm
              rw [Nat.ceil_eq_iff (by positivity)]
              constructor <;> (norm_num; linarith)
            · suffices h : ⌈ ( n : ℚ ) / 2 ^ ( d : ℕ ) ⌉₊ = 2 * x + 1 by
                norm_num [h]
              rw [Nat.ceil_eq_iff (by positivity)]
              constructor <;> (norm_num; linarith)⟩⟩,
    let _ := hn; by simp,
    let _ := hn; by
      dsimp
      congr 1
      rw [Nat.ceil_eq_iff one_ne_zero]
      use by positivity
      exact div_le_one_of_le₀ (mod_cast Nat.le_pow_clog one_lt_two _) (by positivity)⟩

instance : NC1_AND_CircuitFamily.Finite := by
  refine ⟨fun n ↦ ⟨fun i ↦ ?_⟩⟩
  cases n <;> simpa [NC1_AND_CircuitFamily] using Finite.of_fintype _

noncomputable section AristotleLemmas
/-
A version of the NC1 AND circuit for n > 0, avoiding the dependent type issues of the main definition.
-/
open FeedForward CircuitFamily
open scoped BigOperators
def NC1_AND_Circuit_pos (n : ℕ) (hn : 0 < n) : FeedForward (Fin 2) (Fin n) (Fin 1) :=
  { depth := Nat.clog 2 n
    nodes := fun k ↦ Fin ⌈n / (2^k.val : ℚ)⌉₊
    gates := fun d x ↦
      if hx : x.val + 1 = ⌈(n / 2 ^ d.succ.val : ℚ)⌉₊ ∧ ⌈(n / 2 ^ d.val : ℚ)⌉₊ % 2 = 1 then
        ⟨⟨Fin 1, (· 0)⟩, fun _ ↦ ⟨2 * x.val, by
          rw [ eq_comm, Nat.ceil_eq_iff ] at hx <;> norm_num at *;
          rw [ lt_div_iff₀ ] at * <;> norm_cast at * <;> norm_num [ pow_succ' ] at *;
          rw [ Nat.lt_ceil, lt_div_iff₀ ] <;> norm_cast <;> norm_num [ pow_succ' ] at * ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) d.val ]⟩⟩
      else
        ⟨⟨Fin 2, fun x ↦ x 0 * x 1⟩, fun (i : Fin 2) ↦ ⟨2 * x.val + i, by
          have := x.2;
          rw [ Nat.lt_ceil ] at *;
          fin_cases i <;> norm_num [ pow_succ, div_mul_eq_div_div ] at *;
          · linarith;
          · contrapose! hx;
            rw [ eq_comm, Nat.ceil_eq_iff ] <;> norm_num;
            exact ⟨ ⟨ this, by linarith ⟩, by rw [ show ⌈ ( n : ℚ ) / 2 ^ ( d : ℕ ) ⌉₊ = 2 * x + 1 by exact_mod_cast Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by push_cast; linarith, by push_cast; linarith ⟩ ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ⟩⟩⟩
    nodes_zero := by
      norm_num
    nodes_last := by
      norm_num +zetaDelta at *;
      have h_ceil : ⌈(n : ℚ) / 2 ^ Nat.clog 2 n⌉₊ = 1 := by
        rw [ Nat.ceil_eq_iff ] <;> norm_num;
        rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num;
        exact ⟨ hn, Nat.le_pow_clog ( by norm_num ) _ ⟩;
      rw [h_ceil]
  }
/-
Base case for the correctness of the NC1 AND circuit: at depth 0, the nodes are just the inputs.
-/
open FeedForward CircuitFamily in
open scoped BigOperators in
def target_prod (n : ℕ) (inputs : Fin n → Fin 2) (d : ℕ) (i : ℕ) : Fin 2 :=
  ∏ j ∈ Finset.Ico (i * 2^d) (min ((i + 1) * 2^d) n),
      if h : j < n then inputs ⟨j, h⟩ else 1

lemma NC1_AND_Circuit_pos_evalNode_zero (n : ℕ) (hn : 0 < n) (inputs : Fin n → Fin 2)
    (i : Fin ⌈n / (2^0 : ℚ)⌉₊) :
    (NC1_AND_Circuit_pos n hn).evalNode (d := 0) i inputs =
    target_prod n inputs 0 i := by
      -- In the base case, when the depth is zero, the circuit's nodes are just the inputs.
      simp [target_prod, FeedForward.evalNode];
      rw [ min_eq_left ] <;> norm_num;
      · convert rfl;
        split_ifs <;> norm_cast at *;
        · congr;
          · norm_num [ Nat.ceil_eq_iff ];
          · aesop;
        · exact False.elim <| ‹¬ ( i : ℕ ) < n› <| Nat.lt_of_lt_of_le i.2 <| by norm_num;
      · exact Nat.succ_le_of_lt ( Fin.is_lt i |> fun x => x.trans_le <| by norm_num [ hn.ne' ] )
/-
Arithmetic lemma: if ceil(n/2^d) is odd and i is the last index at the next layer, then the second child index at the current layer is out of bounds.
-/
lemma ceil_div_two_pow_odd_implies (n d i : ℕ)
    (h_odd : ⌈(n : ℚ) / 2^d⌉₊ % 2 = 1)
    (h_i : i + 1 = ⌈(n : ℚ) / 2^(d+1)⌉₊) :
    n ≤ (2 * i + 1) * 2^d := by
      rw [ eq_comm, Nat.ceil_eq_iff ] at h_i;
      · rw [ div_le_iff₀, lt_div_iff₀ ] at * <;> norm_cast at * <;> ring_nf at * <;> norm_num at *;
        contrapose! h_odd;
        rw [ show ⌈ ( n : ℚ ) * ( 2 ^ d ) ⁻¹⌉₊ = i * 2 + 2 by
              rw [ Nat.ceil_eq_iff ] <;> norm_num;
              exact ⟨ by rw [ ← div_eq_mul_inv ] ; rw [ lt_div_iff₀ ( by positivity ) ] ; norm_cast; linarith, by rw [ ← div_eq_mul_inv ] ; rw [ div_le_iff₀ ( by positivity ) ] ; norm_cast; linarith ⟩ ] ; norm_num [ Nat.add_mod, Nat.mul_mod ];
      · linarith
/-
The target product for a node at depth d+1 splits into the product of the target products for its children at depth d.
-/
open FeedForward CircuitFamily
open scoped BigOperators
lemma target_prod_split (n : ℕ) (inputs : Fin n → Fin 2) (d i : ℕ) :
    target_prod n inputs (d + 1) i =
    target_prod n inputs d (2 * i) * target_prod n inputs d (2 * i + 1) := by
      unfold target_prod;
      rw [ ← Finset.prod_union ]
      · congr
        ring_nf
        -- The union of the two intervals covers the entire range from the start of the first interval to the end of the second interval.
        ext; simp [Finset.mem_Ico, Finset.mem_union];
        grind;
      · ring_nf
        exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂, min_le_left ( i * 2 ^ d * 2 + 2 ^ d ) n, min_le_left ( i * 2 ^ d * 2 + 2 ^ d * 2 ) n ] ;
/-
If the start index of the target product range is out of bounds, the product is 1.
-/
open FeedForward CircuitFamily
open scoped BigOperators
lemma target_prod_eq_one_of_ge (n : ℕ) (inputs : Fin n → Fin 2) (d i : ℕ) (h : n ≤ i * 2^d) :
    target_prod n inputs d i = 1 := by
      unfold target_prod; aesop;
/-
Inductive step for the correctness of the NC1 AND circuit: if the property holds for layer d, it holds for layer d+1.
-/
open FeedForward CircuitFamily
open scoped BigOperators
lemma NC1_AND_Circuit_pos_evalNode_step (n : ℕ) (hn : 0 < n) (inputs : Fin n → Fin 2)
    (d : Fin (Nat.clog 2 n))
    (IH : ∀ j : Fin ⌈n / (2^d.val : ℚ)⌉₊,
      (NC1_AND_Circuit_pos n hn).evalNode (d := d.castSucc) j inputs = target_prod n inputs d j)
    (i : Fin ⌈n / (2^d.succ.val : ℚ)⌉₊) :
    (NC1_AND_Circuit_pos n hn).evalNode (d := d.succ) i inputs = target_prod n inputs (d + 1) i := by
      unfold NC1_AND_Circuit_pos;
      erw [ evalNode_succ ];
      field_simp;
      split_ifs <;> simp_all +decide [ target_prod_split ];
      · have h_target_prod_zero : target_prod n inputs (d : ℕ) (2 * i + 1) = 1 := by
          apply target_prod_eq_one_of_ge;
          have := ceil_div_two_pow_odd_implies n d i ( by tauto ) ( by tauto ) ; norm_num at * ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) d.val ] ;
        unfold FeedForward.Gate.eval; aesop;
      · convert congr_arg₂ ( · * · ) ( IH ⟨ 2 * i, _ ⟩ ) ( IH ⟨ 2 * i + 1, _ ⟩ ) using 1
/-
The node i at layer d of the NC1_AND circuit computes the AND of the inputs in the range [i*2^d, (i+1)*2^d).
-/
open FeedForward CircuitFamily
open scoped BigOperators
theorem NC1_AND_Circuit_pos_evalNode (n : ℕ) (hn : 0 < n) (inputs : Fin n → Fin 2)
    (d : Fin (Nat.clog 2 n + 1)) (i : Fin ⌈n / (2^d.val : ℚ)⌉₊) :
    (NC1_AND_Circuit_pos n hn).evalNode (d := d) i inputs =
    target_prod n inputs d i := by
  revert i
  refine Fin.induction ?_ ?_ d
  · intro i
    apply NC1_AND_Circuit_pos_evalNode_zero
  · intro d IH i
    apply NC1_AND_Circuit_pos_evalNode_step
    exact IH
end AristotleLemmas

theorem NC1_AND_CircuitFamily_computes : NC1_AND_CircuitFamily.computes₁ FuncFamily₁.AND := by
  unfold NC1_AND_CircuitFamily CircuitFamily₁.computes₁
  intro n; by_cases hn : n = 0
  · bound;
  · simp [hn]
    unfold FeedForward.eval₁ FuncFamily₁.AND FeedForward.eval;
    funext xs;
    convert NC1_AND_Circuit_pos_evalNode n ( Nat.pos_of_ne_zero hn ) xs ⟨ Nat.clog 2 n, Nat.lt_succ_self _ ⟩ ⟨ 0, Nat.pos_of_ne_zero _ ⟩;
    all_goals norm_num [ target_prod ];
    · convert congr_arg Fin.val ( show (_ : Fin 1) = 0 from Fin.ext <| by aesop );
      rw [ Nat.ceil_eq_iff ] <;> norm_num;
      field_simp;
      exact ⟨ Nat.pos_of_ne_zero hn, mod_cast Nat.le_pow_clog ( by decide ) _ ⟩;
    · rw [ min_eq_right ];
      · simp [Finset.prod_range]
      · exact Nat.le_pow_clog ( by decide ) _;
    · positivity

noncomputable section AristotleLemmas

lemma NC1_AND_size_mem_poly : (fun n ↦ (NC1_AND_CircuitFamily n).size) ∈ GrowthRate.linear := by
  simp [GrowthRate.linear, GrowthRate.bigO, Asymptotics.isBigO_iff ]
  use 4, 1
  intro b hb; norm_cast; rcases eq_or_ne b 0 <;> simp_all +decide [ NC1_AND_CircuitFamily ] ;
  -- Let's simplify the expression for the size.
  have h_size : ∑ x ∈ Finset.range (Nat.clog 2 b), ⌈(b : ℚ) / 2 ^ (x + 1)⌉₊ ≤ b * (∑ x ∈ Finset.range (Nat.clog 2 b), (1 / 2 : ℚ) ^ (x + 1)) + Nat.clog 2 b := by
    push_cast [ Finset.mul_sum _ _ _ ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => show ( ⌈ ( b : ℚ ) / 2 ^ ( _ + 1 ) ⌉₊ : ℚ ) ≤ ( b : ℚ ) * ( 1 / 2 ) ^ ( _ + 1 ) + 1 by exact le_trans ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) ( by ring_nf; norm_num ) ) ( by simp +decide [ Finset.sum_add_distrib ] );
  -- Let's simplify the geometric series sum.
  have h_geo_series : ∑ x ∈ Finset.range (Nat.clog 2 b), (1 / 2 : ℚ) ^ (x + 1) ≤ 1 := by
    ring_nf;
    rw [ ← Finset.sum_mul _ _ _, geom_sum_eq ] <;> ring_nf <;> norm_num;
  -- Let's simplify the logarithmic term.
  have h_log_term : Nat.clog 2 b ≤ b := by
    -- By induction on $b$, we can show that $2^b \geq b$ for all $b \geq 1$.
    have h_ind : ∀ b : ℕ, 1 ≤ b → 2 ^ b ≥ b := by
      exact fun n hn => by induction hn <;> norm_num [ pow_succ' ] at * ; linarith;
    exact le_trans ( Nat.clog_mono_right _ ( h_ind _ hb ) ) ( by norm_num );
  norm_num [ FeedForward.size ] at *;
  norm_num [ Finset.sum_range, Fin.sum_univ_succ ] at *;
  rw [ ← @Nat.cast_le ℚ ] ; push_cast ; nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ b ), ( by norm_cast : ( Nat.clog 2 b : ℚ ) ≤ b ) ]

lemma NC1_AND_depth_mem_log : (fun n ↦ (NC1_AND_CircuitFamily n).depth) ∈ GrowthRate.bigO Nat.log2 := by
  apply Asymptotics.IsBigO.of_bound 2 _
  -- For n ≥ 4, we have log2 n ≤ 2 * log2 n, which implies clog2 n ≤ 2 * log2 n.
  have h_log2_le : ∀ n ≥ 4, Nat.clog 2 n ≤ 2 * Nat.log2 n := by
    intro n hn
    have h_log2_le : Nat.clog 2 n ≤ Nat.log2 n + 1 := by
      rw [ Nat.clog_le_iff_le_pow ] <;> norm_num;
      rw [ Nat.le_iff_lt_or_eq, ← Nat.log_lt_iff_lt_pow one_lt_two (by omega) ]
      rw [ Nat.lt_succ_iff, Nat.le_log2 ] <;> norm_num;
      · exact Or.inl ( Nat.pow_log_le_self 2 ( by linarith ) );
      · grind;
    rw [ Nat.le_iff_lt_or_eq ] at *;
    cases h_log2_le
    · grind;
    · rcases k : Nat.log2 n with ( _ | _ | k )
      · simp_all [Nat.log2]
        rcases n with ( _ | _ | _ | n ) <;> simp_all
        cases n <;> contradiction;
      · simp_all [ Nat.log2 ];
      · simp_all +arith +decide [ Nat.log2 ];
  norm_num +zetaDelta at *;
  refine ⟨ 4, fun n hn => ?_ ⟩
  norm_cast
  unfold NC1_AND_CircuitFamily
  aesop

end AristotleLemmas

theorem NC1_AND_hasDepth_mem_log : NC1_AND_CircuitFamily.hasDepth GrowthRate.log := by
  rw [← GrowthRate.bigO_log2_eq_log]
  exact NC1_AND_depth_mem_log

noncomputable section AristotleLemmas

lemma sum_ceil_div_two_pow_le (n d : ℕ) :
    ∑ i ∈ Finset.range d, ⌈(n : ℚ) / 2^(i+1)⌉₊ ≤ n + d := by
  rw [ add_comm, ← Nat.cast_le (α := ℚ )]
  -- The sum of the terms $n / (2^i)$ from $i=0$ to $d-1$ is a geometric series with sum $n * (1 - (1/2)^d) / (1 - 1/2) = 2n * (1 - (1/2)^d)$.
  have h_geo_sum : ∑ i ∈ Finset.range d, (n : ℚ) / 2 ^ (i + 1) = 2 * n * (1 - (1 / 2 : ℚ) ^ d) / 2 := by
    ring_nf
    rw [← Finset.sum_mul, ← Finset.mul_sum, geom_sum_eq] <;> ring_nf
    norm_num
  have h_geo_sum_le : ∑ i ∈ Finset.range d, ⌈(n : ℚ) / 2 ^ (i + 1)⌉₊ ≤ ∑ i ∈ Finset.range d, (n : ℚ) / 2 ^ (i + 1) + d := by
    push_cast;
    exact le_trans ( Finset.sum_le_sum fun _ _ => Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) ( by simp +decide [ Finset.sum_add_distrib ] );
  exact h_geo_sum_le.trans ( by rw [ h_geo_sum ] ; push_cast; nlinarith [ show ( 1 / 2 : ℚ ) ^ d ≥ 0 by positivity ] )

lemma NC1_AND_size_bound (n : ℕ) : (NC1_AND_CircuitFamily n).size ≤ n + Nat.clog 2 n + 1 := by
  by_contra h;
  -- Let's simplify the goal using the definition of `size`.
  unfold NC1_AND_CircuitFamily at h;
  split_ifs at h <;> simp_all [ FeedForward.size ];
  have := sum_ceil_div_two_pow_le n ( Nat.clog 2 n ) ; simp_all [ Finset.sum_range ];
  grind

end AristotleLemmas

/-- The AND problem is contained in NC₁, because we can make a log-depth tree of ANDs. -/
theorem AND_mem_NCi_1 : FuncFamily₁.AND ∈ NCi 1 := by
  simp_rw [NCi, pow_one, GrowthRate.bigO_log2_eq_log, mem_circuitClass_iff (Fin 1)]
  refine ⟨NC1_AND_CircuitFamily, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact NC1_AND_CircuitFamily_computes
  · open GrowthRate in exact
      quasilinear_subset_poly
      <| linearithmic_subset_quasilinear
      <| linear_subset_linearithmic
      <| NC1_AND_size_mem_poly
  · exact NC1_AND_hasDepth_mem_log
  · intro n d node
    simp only [NC1_AND_CircuitFamily]
    cases n <;> grind [NC_GateOps]
