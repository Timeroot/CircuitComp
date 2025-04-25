import CircuitComp.Basic

open FeedForward
open CircuitFamily

/-- A fairly minimal set of gates for NC classes: just NOT and AND. -/
def NC₀_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Unit, fun x ↦ 1 - x ()⟩, --NOT
  ⟨Fin 2, fun x ↦ x 0 * x 1⟩} --AND

/-- The circuit class of nonuniform NC⁰: constant depth polynomial-size circuits with
fanin-2 NOTs and ANDs. -/
def NC₀ : Set (FuncFamily (Fin 2)) :=
  fun fs ↦ ∃ (CF : CircuitFamily (Fin 2)),
    CF.computes fs
    ∧ CF.sizePoly
    ∧ CF.depthBigO 1
    ∧ CF.onlyUsesGates NC₀_GateOps

/-- The circuit class of nonuniform NCi: polynomial-size circuits with
fanin-2 NOTs and ANDs, and depth O(logⁱ n). -/
def NCi (i : ℕ) : Set (FuncFamily (Fin 2)) :=
  fun fs ↦ ∃ (CF : CircuitFamily (Fin 2)),
    CF.computes fs
    ∧ CF.sizePoly
    ∧ CF.depthBigO ((Nat.log2 ·) ^ i)
    ∧ CF.onlyUsesGates NC₀_GateOps

/-- NC₀ is the 0th element of the NCi hierarchy -/
theorem NCi_zero : NCi 0 = NC₀ := by
  rfl --Wait, this actually holds by definitional equality? That's hilarious

/-- The definition of NCi is unchanged if you exchange the gates for any *finite* set of gates. -/
theorem NCi_other_gates (S : Set (GateOp (Fin 2))) (hS₁ : Finite S) (hS₂ : NC₀_GateOps ⊆ S) :
    NCi i = (fun fs ↦ ∃ (CF : CircuitFamily (Fin 2)),
    CF.computes fs
    ∧ CF.sizePoly
    ∧ CF.depthBigO ((Nat.log2 ·) ^ i)
    ∧ CF.onlyUsesGates S)
   := by
  sorry

/-- The problem AND: Compute the logical AND of the input bits. -/
def and_family : FuncFamily (Fin 2) :=
  fun _ xs ↦ ∏ i, xs i

/-- The AND problem is not in the class NC₀, because NC₀ only has functions
of bounded support, and AND is arbitrarilty large support. -/
theorem AND_not_mem_NC₀ : and_family ∉ NC₀ := by
  sorry

/-- The AND problem is contained in NC₁, because we can make a log-depth tree of ANDs. -/
theorem AND_mem_NCi_1 : and_family ∈ NCi 1 := by
  sorry
