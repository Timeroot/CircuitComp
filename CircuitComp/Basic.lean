import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Card

import CircuitComp.GrowthRate
import CircuitComp.FuncFamily

universe u v

/-- A single operation in a `FeedForward` circuit. With arity `ι`, it is a function from
several `α`'s to `α`. For instance, "3-input AND" could be one op. -/
structure FeedForward.GateOp (α : Type u) where
  ι : Type u
  func : (ι → α) → α

/-- A single gate in a `FeedForward` circuit. It describes how a `GateOp` is connected to
the nodes in `domain`. For instance, `AND(v₁, v₅, v₇)` could be one Gate. -/
structure FeedForward.Gate (α : Type u) (domain : Type v) where
  op : FeedForward.GateOp α
  inputs : op.ι → domain

/-- A `FeedForward` circuit consists of a series of gates (or "ops", in ML language)
that rely on the values computed at earlier layers. Each value is from the type `α`,
and the inputs and outputs have types `inp` and `out`.

This makes no assumption as to the (horizontal) finiteness of the circuit.
-/
structure FeedForward (α : Type u) (inp : Type v) (out : Type v) where
  /- How many layers of gates there are. The inputs are layer 0, so this means `depth+1`
  layers of values. -/
  depth : ℕ
  /- The set of nodes at each layer. The zeroth layer is the input. -/
  nodes : Fin (depth + 1) → Type v
  /- The gates at each nonzero layer. -/
  gates : (d : Fin depth) → (nodes d.succ) → FeedForward.Gate α (nodes d.castSucc)
  /- Guarantee the input and output types are correct -/
  hIn : nodes 0 = inp
  hOut : nodes (Fin.last depth) = out

namespace FeedForward

variable {α : Type u} {inp out : Type v} (F : FeedForward α inp out)

def Gate.eval {domain : Type*} (g : FeedForward.Gate α domain) (xs : domain → α) : α :=
  g.op.func (xs <| g.inputs ·)

/-- Evaluate a `FeedForward` on some input data and get a particular node's value -/
def evalNode {d : Fin (F.depth + 1)} (node : F.nodes d) (xs : inp → α) : α := by
  rcases d with ⟨d, hd⟩
  induction d
  · exact xs (F.hIn ▸ node)
  · rename_i d' ih
    apply (F.gates ⟨d', Nat.succ_lt_succ_iff.mp hd⟩ node).eval
    exact fun node' ↦ ih (Nat.lt_of_succ_lt hd) node'

/-- Evaluate a `FeedForward` on some input data. Gives a value for each node at the last layer. -/
def eval (xs : inp → α) : out → α :=
  fun n ↦ F.evalNode (d := (Fin.last F.depth)) (F.hOut.symm.rec n) xs

/-- Evaluate a `FeedForward` on some input data, and get the unique output. -/
def eval₁ [Unique out] (xs : inp → α) : α :=
  F.eval xs default

/-- The cardinal width of a feedforward circuit is the largest number of nodes in any layer. -/
noncomputable def width_card : Cardinal :=
  ⨆ d, Cardinal.mk (F.nodes d)

/-- The size of a feedforward circuit is the total number of gates. Note that if any layer is
infinite, the whole sum will be zero. -/
noncomputable def size : ℕ :=
  Nat.card (@Sigma (Fin F.depth) (fun d ↦ F.nodes d.succ))

def finite : Prop :=
  ∀ i, Finite (F.nodes i)

/-- A `FeedForward` is said to `onlyUsesGates` from a set of `GateOp`s if every gate is one of those. -/
def onlyUsesGates (S : Set (GateOp α)) : Prop :=
  ∀ d n, (F.gates d n).op ∈ S

variable {F} {S T : Set (GateOp α)}

theorem onlyUsesGates_mono (hS : S ⊆ T) (hF : F.onlyUsesGates S) :
    F.onlyUsesGates T := by
  intro d n
  specialize hF d n
  exact hS hF

end FeedForward

open FeedForward

/-- A `CircuitFamily` is a collection of `FeedForward` circuits parameterized by an input size `n`.
The `n`th circuit must have input type `Fin n`, and a `Unit` output. -/
def CircuitFamily (α : Type u) :=
  (n : ℕ) → FeedForward α (Fin n) Unit

namespace CircuitFamily

variable {α : Type u} {inp out : Type v} (CF : CircuitFamily α)

/-- A `CircuitFamily` is said to `computes` a function family if that is given by its `eval₁`.-/
def computes (F : FuncFamily α) : Prop :=
  ∀ n, (CF n).eval₁ = F n

/-- Predicate expressing that the depth grows as O(f n). -/
def hasDepth (f : GrowthRate) : Prop :=
  (fun n ↦ (CF n).depth) ∈ f

/-- Predicate expressing that all circuits in the family are finite. -/
def finite : Prop :=
  ∀ n, (CF n).finite

/-- Predicate expressing that the size grows as O(f n). -/
def hasSize (f : GrowthRate) : Prop :=
  CF.finite ∧ (fun n ↦ (CF n).size) ∈ f

/-- A `CircuitFamily` is said to `onlyUsesGates` from a set of `GateOp`s if every gate is one of those. -/
def onlyUsesGates (S : Set (GateOp α)) : Prop :=
  ∀ n, (CF n).onlyUsesGates S

variable {CF} {S T : Set (GateOp α)}

theorem onlyUsesGates_mono (hS : S ⊆ T) (hCF : CF.onlyUsesGates S) :
  CF.onlyUsesGates T := by
  intro n
  exact FeedForward.onlyUsesGates_mono hS (hCF n)

end CircuitFamily

open CircuitFamily

/-- A `CircuitClass` is a set of function families defined by circuits on a given set of gates,
a bound on depth, and a bound on size. -/
def CircuitClass {α : Type*} (size : GrowthRate) (depth : GrowthRate) (gates : Set (GateOp α))
    : Set (FuncFamily α) :=
  fun fs ↦ ∃ (CF : CircuitFamily α),
    CF.computes fs
    ∧ CF.hasSize size
    ∧ CF.hasDepth depth
    ∧ CF.onlyUsesGates gates

namespace CircuitClass

variable {α : Type*} (size : GrowthRate) (depth : GrowthRate) (gates : Set (GateOp α))

theorem Monotone_size : Monotone fun s ↦ CircuitClass s depth gates := by
  rintro s₁ s₂ hs fs ⟨CF, hCF₁, hCF₂, hCF₃, hCF₄⟩
  exact ⟨CF, hCF₁, ⟨hCF₂.1, hs hCF₂.2⟩, hCF₃, hCF₄⟩

theorem Monotone_depth : Monotone fun d ↦ CircuitClass size d gates := by
  rintro d₁ d₂ hd fs ⟨CF, hCF₁, hCF₂, hCF₃, hCF₄⟩
  exact ⟨CF, hCF₁, hCF₂, hd hCF₃, hCF₄⟩

theorem Monotone_gates : Monotone fun (g : Set (GateOp α)) ↦ CircuitClass size depth g := by
  rintro g₁ g₂ hg fs ⟨CF, hCF₁, hCF₂, hCF₃, hCF₄⟩
  exact ⟨CF, hCF₁, hCF₂, hCF₃, onlyUsesGates_mono hg hCF₄⟩

end CircuitClass
