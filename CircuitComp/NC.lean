import CircuitComp.Circuit
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Nat.Log

open FeedForward
open CircuitFamily

/-- A fairly minimal set of gates for NC classes: just NOT and AND. -/
def NC₀_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Fin 1, (· 0)⟩, --Id
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

/-- The definition of NCi is unchanged if you add any larger *finite* set of gates. -/
theorem NCi_other_gates (S : Set (GateOp (Fin 2))) (hS₁ : Finite S) (hS₂ : NC₀_GateOps ⊆ S) :
    NCi i = CircuitClass .poly (.bigO (Nat.log2 · ^ i)) S
   := by
  sorry

/-- Any function family in NC₀ has a bounded arity (more precisely, a bounded size `EssDomain`). -/
theorem bounded_essDomain_of_mem_NC₀ {fn : FuncFamily (Fin 2)} (h : fn ∈ NC₀) :
    ∃ k, ∀ n, (fn n).EssDomain.ncard ≤ k := by
  sorry

/-- The AND problem is not in the class NC₀, because NC₀ only has functions
of bounded support, and AND is arbitrarilty large support. -/
theorem AND_not_mem_NC₀ : FuncFamily.AND ∉ NC₀ := by
  intro h
  obtain ⟨k, hk⟩ := bounded_essDomain_of_mem_NC₀ h
  specialize hk (k+1)
  rw [FuncFamily.AND_EssDomain] at hk
  simp [Set.ncard_univ] at hk

--TODO pull out
theorem and_iff_and_imp {a b : Prop} : (a ∧ b) ↔ (a ∧ (a → b)) := by
  tauto

/-- The AND problem is contained in NC₁, because we can make a log-depth tree of ANDs. -/
theorem AND_mem_NCi_1 : FuncFamily.AND ∈ NCi 1 := by
  --Prove by constructing the circuit
  use (by
    intro n --for each n, construct a circuit
    use Nat.clog 2 n--depth
      --the width at layer k is n/2^k, at the last layer this means we're `Fin 1`.
    · use fun k ↦ Fin ⌈n / (2^k.val : ℝ)⌉₊
    ·  --describe the gates at each layer
      intro d x
      -- split_ifs at x with h
      -- · use ⟨_, (· ())⟩ --at the last layer, we have an `Id` gate from Fin 1 to Fin 1
      --   intro
      --   exact cast (by rw [if_neg]; sorry; sorry) (0 : Fin 1)
      --at all other layers, we take an AND-2 gate from indices `2x` and `2x+1` to `x`.
      by_cases hx : x.val + 1 = ⌈↑n / 2 ^ d.succ.val⌉₊ ∧ (⌈↑n / 2 ^ d.val⌉₊ % 2 == 1)
      · --Well, if x is the last one in its layer and the parent layer is odd,
        --then we just use an identity gate.
        use ⟨_, (· 0)⟩
        intro
        exact ⟨2*x.val, by sorry⟩
      · --otherwise we take the AND
        use ⟨Fin 2, fun x ↦ x 0 * x 1⟩
        intro (i : Fin 2)
        exact ⟨2*x.val + i, by sorry⟩
    · simp
    · congr 1
      simp
      sorry
  )
  --Split up the four conditions on the family
  refine .intro ?_ <| .intro ?_ <| .intro ?_ ?_
  · --Show that the circuit above actually computes the thing we want it to
    sorry
  · constructor
    · dsimp [CircuitFamily.finite, FeedForward.finite]
      infer_instance
    · dsimp [size]
      conv =>
        enter [2, n]
        rw [@Nat.card_sigma _ _ _ ?_]
        rfl
        tactic =>
          infer_instance
      sorry
  · dsimp [hasDepth]
    --TODO should be simp
    sorry
  · intro _ _ _
    dsimp
    split
    · simp [NC₀_GateOps]
      sorry
    simp [NC₀_GateOps]
