import CircuitComp.FuncFamily

import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

noncomputable section

/-- A layered branching program, operating on variables indexed by a type `α`, each taking
a value in `β`, with natural number-indexed layers. The nodes at each layer are taken to be
a type in the same universe as `β`, which is sufficient in general. The program then returns
a value in `γ`.

Two assumptions this form does not make:
1. We do not assume that the nodes at each layer are finite. We have the predicate
  `LayeredBranchingProgram.Finite` for this. Not building this into the structure lets us talk about
  branching programs that respond to infinite inputs, such as branching programs on the natural numbers.
2. We do not assume that the branching program uses the same variable for all nodes in the same layer.
  We have the predicate `LayeredBranchingProgram.IsOblivious` for this. This is often implict in literature
  when discussing "layered branching programs", and often it's equivalent up to a modest increase in depth
  and width, but there are other cases (like the Read-Once Branching Program literature) where the difference
  matters quite a bit.
-/
structure LayeredBranchingProgram (α : Type u) (β : Type v) (γ : Type w) where
  /- The number of layers in the program. We use the convention that `depth = 0` means
  that there is only the input layer; this avoids some awkward issues with `NeZero depth`
  instances or tracking when an index is properly in bounds. -/
  depth : ℕ
  /- The set of nodes in each layer. -/
  nodes (n : Fin depth.succ) : Type v
  /- The variable that each node depends on. -/
  nodeVar {n : Fin depth} : nodes n.castSucc → α
  /- The outgoing edges from each node. -/
  edges {n : Fin depth} : nodes n.castSucc → β → nodes n.succ
  /- The proposition that the starting node is unique.-/
  startUnique : Unique (nodes 0)
  /- The end nodes each return a value in `γ`. -/
  retVals : nodes (Fin.last depth) → γ

namespace LayeredBranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w} (P : LayeredBranchingProgram α β γ)

attribute [instance] LayeredBranchingProgram.startUnique

/-- We call a branching program finite if the nodes at each layer is finite. -/
protected class Finite : Prop where
  finite : ∀ i, Finite (P.nodes i)

instance [inst : P.Finite] {i} : Finite (P.nodes i) :=
  inst.finite i

def start : P.nodes 0 :=
  P.startUnique.default

/-- We say a branching program is oblivious if all nodes in the same layer read the same variable.
This is often implicit in the "layered" adjective of a layered branching program. -/
def IsOblivious : Prop :=
  ∀ i : Fin P.depth, ∀ j k : P.nodes i.castSucc, P.nodeVar j = P.nodeVar k

/-- The width of a branching program is the maximum number of nodes in any layer. -/
def width : ℕ :=
  ⨆ i : Fin P.depth.succ, Nat.card (P.nodes i)

/-- The size of a branching program is the total number of nodes. -/
noncomputable def size : ℕ :=
  Nat.card (Sigma P.nodes)

theorem size_eq_sum_card_nodes [P.Finite] :
    P.size = ∑ i, Nat.card (P.nodes i) :=
  Nat.card_sigma

theorem size_le_width_mul_depth [P.Finite] :
    P.size ≤ P.width * P.depth + 1 := by
  have h_depth_0 : Nat.card (P.nodes 0) = 1 :=
   Nat.card_unique
  have h_depth_succ : ∀ i : Fin P.depth, Nat.card (P.nodes i.succ) ≤ P.width := by
    intro i
    rw [width]
    sorry
  rw [size_eq_sum_card_nodes]
  sorry

/-- Given a valuation `x` of the input variables, evaluate the layer `d` of the branching program.
Returns the selected node at layer `d`. -/
def evalLayer (d : Fin P.depth.succ) (x : α → β) : P.nodes d :=
  d.inductionOn P.start fun _ a ↦ P.edges a (x (P.nodeVar a))

theorem evalLayer_zero (x : α → β) : P.evalLayer 0 x = P.start := by
  rfl

theorem evalLayer_succ (d : Fin P.depth) (x : α → β) :
    P.evalLayer d.succ x =
    P.edges (P.evalLayer d.castSucc x) (x (P.nodeVar (P.evalLayer d.castSucc x))) := by
  rfl

/-- Evaluate a branching program on an input valuation `x`. -/
def eval (x : α → β) : γ :=
  P.retVals (P.evalLayer (Fin.last P.depth) x)

def computes (P : LayeredBranchingProgram α β γ) (F : (α → β) → γ) : Prop :=
  ∀ x, P.eval x = F x

/-- Every function can be computed by an oblivious branching program of exponential size and constant width. -/
theorem computes_const_width [Fintype α] [Fintype β] [Fintype γ] (F : (α → β) → γ) :
    ∃ P : LayeredBranchingProgram α β γ,
      P.computes F ∧
      P.Finite ∧
      P.IsOblivious ∧
      P.width ≤ Fintype.card γ + 1 ∧
      P.depth ≤ Fintype.card α * (Fintype.card β ^ Fintype.card α) := by
  sorry

/-- A boolean function can be computed in O(n * 2^n) depth and width 3.-/
theorem computes_bool_width_3 [Fintype α] [Fintype β] [Fintype γ] (F : (α → Bool) → Bool) :
    ∃ P : LayeredBranchingProgram α Bool Bool,
      P.computes F ∧
      P.Finite ∧
      P.IsOblivious ∧
      P.width ≤ 3 ∧
      P.depth ≤ Fintype.card α * 2 ^ Fintype.card α :=
  computes_const_width F

/-- Every function can be computed by an oblivious branching program of linear depth and exponential size. -/
theorem computes_linear_depth [Fintype α] [Fintype β] [Fintype γ] (F : (α → β) → γ) :
    ∃ P : LayeredBranchingProgram α β γ,
      P.computes F ∧
      P.Finite ∧
      P.IsOblivious ∧
      P.depth ≤ Fintype.card α ∧
      P.size ≤ 2 * Fintype.card β ^ Fintype.card α := by
  sorry

/-- Every (not necessarily `IsOblivious`) layered branching program can be converted to a branching program
that `IsOblivious`, with at most a linear factor increase in depth (linear in the number of variables) and
a doubling of width. -/
theorem oblivious_of_nonoblivious [Fintype α] [Fintype β] [Fintype γ] (P : LayeredBranchingProgram α β γ) :
    ∃ P' : LayeredBranchingProgram α β γ,
      P'.eval = P.eval ∧
      P'.depth ≤ Fintype.card α * P.depth ∧
      P'.width ≤ 2 * P.width := by
  sorry
