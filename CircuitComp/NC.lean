import CircuitComp.Circuit
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Nat.Log

open FeedForward
open CircuitFamily

/-- A fairly minimal set of gates for NC classes: just NOT and AND. Technically, we also need the
identity gate (for forwarding operations between layers) and a constant gate (for the 0-ary case). -/
def NC₀_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Fin 0, 1⟩, --Constant one gate
   ⟨Fin 1, (· 0)⟩, --Id
   ⟨Fin 1, fun x ↦ 1 - x 0⟩, --NOT
  ⟨Fin 2, fun x ↦ x 0 * x 1⟩} --AND

/-- The circuit class of nonuniform NC⁰: constant depth polynomial-size circuits with
fanin-2 NOTs and ANDs. -/
def NC₀ : Set (FuncFamily (Fin 2)) :=
  CircuitClass .poly .const NC₀_GateOps

/-- The circuit class of nonuniform NCi: polynomial-size circuits with
NOTs and fanin-2 ANDs, and depth O(logⁱ n). -/
def NCi (i : ℕ) : Set (FuncFamily (Fin 2)) :=
  CircuitClass .poly (.bigO (Nat.log2 · ^ i)) NC₀_GateOps

/-- NC₀ is the 0th element of the NCi hierarchy -/
theorem NCi_zero : NCi 0 = NC₀ := by
  rfl --Wait, this actually holds by definitional equality? That's hilarious

def NC : Set (FuncFamily (Fin 2)) :=
  ⋃ i, NCi i

theorem NCi_subset_NC (i : ℕ) : NCi i ⊆ NC :=
  Set.subset_iUnion_of_subset i fun _ ↦ id

/-- All gates in `NC₀_GateOps` have fan-in at most 2. -/
lemma NC₀_fanin_le_2 : ∀ op ∈ NC₀_GateOps, Finite op.ι ∧ Nat.card op.ι ≤ 2 := by
  unfold NC₀_GateOps
  aesop (add safe Finite.of_fintype)

/-- Any function family in NC₀ has a bounded arity (more precisely, a bounded size `EssDomain`). -/
theorem bounded_essDomain_of_mem_NC₀ {fn : FuncFamily (Fin 2)} (h : fn ∈ NC₀) :
    ∃ k, ∀ n, (fn n).EssDomain.ncard ≤ k := by
  obtain ⟨CF, hCF₁, hCF₂, hCF₃, hCF₄⟩ := h
  obtain ⟨C, hC⟩ := GrowthRate.bounded_of_const hCF₃
  use 2 ^ C
  intro n
  have h_essDomain_subset_inputDeps : (fn n).EssDomain ⊆ (CF n).inputDeps
      (Fin.last (CF n).depth) (CF n |> FeedForward.nodes_last |> fun h => h.symm.rec default) := by
    rw [← hCF₁ n]
    unfold FeedForward.eval₁
    convert FeedForward.essDomain_subset_inputDeps _
  apply (Set.ncard_le_ncard h_essDomain_subset_inputDeps).trans
  refine ((CF n).inputDeps_card_le _ 2 ?_).trans ?_
  · exact fun d n_2 ↦ NC₀_fanin_le_2 ((CF n).gates d n_2).op (hCF₄ n d n_2);
  · exact pow_le_pow_right₀ one_le_two (hC n)

/-- The AND problem is not in the class NC₀, because NC₀ only has functions
of bounded support, and AND is arbitrarilty large support. -/
theorem AND_not_mem_NC₀ : FuncFamily.AND ∉ NC₀ := by
  intro h
  obtain ⟨k, hk⟩ := bounded_essDomain_of_mem_NC₀ h
  specialize hk (k+1)
  rw [FuncFamily.AND_EssDomain] at hk
  simp [Set.ncard_univ] at hk

/-- The definition of NCi is unchanged if you add any larger *finite* set of
  *finite arity* gates. -/
theorem NCi_other_gates {i : ℕ} {S : Set (GateOp (Fin 2))} [Finite S] (hS : NC₀_GateOps ⊆ S)
    (hS₂ : ∀ s ∈ S, Finite s.ι) :
    NCi i = CircuitClass .poly (.bigO (Nat.log2 · ^ i)) S := by
  sorry

/-- The AND problem is contained in NC₁, because we can make a log-depth tree of ANDs. -/
theorem AND_mem_NCi_1 : FuncFamily.AND ∈ NCi 1 := by
  --Prove by constructing the circuit
  use (by
    intro n --for each n, construct a circuit
    by_cases n = 0
    · --The 0-bit input case
      fconstructor
      · exact 1 --depth 1
      · exact fun i ↦ Fin i.val --width 1 on its only layer. width 0 at input.
      · exact fun _ _ ↦ ⟨⟨Fin 0, 1⟩, Fin.elim0⟩ -- a single constant "1" gate
      · subst n; rfl
      · simp
    fconstructor
    · --depth
      exact Nat.clog 2 n
    · --the width at layer k is n/2^k, at the last layer this means we're `Fin 1`.
      exact fun k ↦ Fin ⌈n / (2^k.val : ℚ)⌉₊
    · --describe the gates at each layer
      --at each layer, we take an AND-2 gate from indices `2x` and `2x+1` to `x`.
      intro d x
      by_cases hx : x.val + 1 = ⌈(n / 2 ^ d.succ.val : ℚ)⌉₊ ∧ (⌈(n / 2 ^ d.val : ℚ)⌉₊ % 2 = 1)
      · --Well, if x is the last one in its layer and the parent layer is odd,
        --then we just use an identity gate.
        use ⟨Fin 1, (· 0)⟩
        intro (_ : Fin 1)
        use 2 * x.val
        simp only [Fin.val_succ, Fin.coe_castSucc] at hx ⊢
        sorry
      · --otherwise we take the AND
        use ⟨Fin 2, fun x ↦ x 0 * x 1⟩
        intro (i : Fin 2)
        use 2 * x.val + i
        simp only [Fin.val_succ, Fin.coe_castSucc] at hx ⊢
        sorry
    · simp
    · congr 1
      simp
      sorry
  )
  --Split up the four conditions on the family
  refine .intro ?_ <| .intro ?_ <| .intro ?_ ?_
  · --Show that the circuit above actually computes the thing we want it to
    admit
  · constructor
    · dsimp [CircuitFamily.finite, FeedForward.finite]
      rintro (_ | n)
      · simp
        exact ⟨inferInstance, inferInstance⟩
      simp
      infer_instance
    · simp [size, GrowthRate.poly]
      use 1
      simp
      sorry
  · dsimp [hasDepth]
    simp only [pow_one, GrowthRate.bigO_log2_eq_log]
    have := GrowthRate.clog_mem_log2
    simp [GrowthRate.log, GrowthRate.bigO]
    sorry
  · intro n d node
    rcases n with _ | n
    · dsimp at d node ⊢
      simp [NC₀_GateOps]
    dsimp at d node ⊢
    split
    · simp [NC₀_GateOps]
    simp [NC₀_GateOps]
