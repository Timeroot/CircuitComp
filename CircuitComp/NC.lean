import CircuitComp.Basic
import Mathlib.Data.Finset.BooleanAlgebra

open FeedForward
open CircuitFamily

/-- A fairly minimal set of gates for NC classes: just NOT and AND. -/
def NC₀_GateOps : Set (GateOp (Fin 2)) :=
  {⟨Unit, fun x ↦ 1 - x ()⟩, --NOT
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

/-- The AND problem is contained in NC₁, because we can make a log-depth tree of ANDs. -/
theorem AND_mem_NCi_1 : FuncFamily.AND ∈ NCi 1 := by
  sorry
