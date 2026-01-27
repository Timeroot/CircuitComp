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
    apply le_ciSup (Finite.bddAbove_range fun i => Nat.card (P.nodes i)) (Fin.succ i)
  have h_sum_bound : ∑ i, Nat.card (P.nodes i) = 1 + ∑ i, Nat.card (P.nodes (Fin.succ i)) := by
    simp [Fin.sum_univ_succ]
  have h_sum_le : ∑ i : Fin P.depth, Nat.card (P.nodes (Fin.succ i)) ≤ P.depth * P.width := by
    exact (Finset.sum_le_sum fun _ _ ↦ h_depth_succ _).trans (by simp)
  linarith [size_eq_sum_card_nodes P]

theorem size_ge_one {α β γ} (P : LayeredBranchingProgram α β γ) [P.Finite] : 1 ≤ P.size := by
  -- Since `nodes 0` is nonempty and finite, its cardinality is at least 1.
  have h_card_0 : 1 ≤ Nat.card (P.nodes 0) := by
    aesop;
  refine' le_trans h_card_0 _;
  have h_card_0 : Nat.card (P.nodes 0) ≤ Nat.card (Sigma P.nodes) := by
    have h_inj : Function.Injective (fun x : P.nodes 0 => ⟨0, x⟩ : P.nodes 0 → Sigma P.nodes) := by
      aesop_cat
    have h_finite : ∀ i : Fin P.depth.succ, Finite (P.nodes i) := by
      exact fun i => by cases ‹P.Finite›; aesop;
    exact Nat.card_le_card_of_injective (fun x ↦ ⟨0, x⟩) h_inj;
  exact h_card_0

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

section canonicalBP

variable [Fintype α] (F : (α → β) → γ)

/--
Construct a canonical branching program for a function F. It queries variables in a fixed order
and stores the values in the nodes. It branches exponentially wide.
-/
def canonicalBP : LayeredBranchingProgram α β γ :=
  letI n := Fintype.card α
  letI e := Fintype.equivFin α
  { depth := n
    nodes i := Fin i → β
    nodeVar {i} _ := e.symm ⟨i, i.is_lt⟩
    edges {i} f b j := if h : j.val < i.val then f ⟨j.val, h⟩ else b
    startUnique := {
      default := Fin.elim0,
      uniq := fun _ ↦ funext fun i ↦ Fin.elim0 i
    }
    retVals f := F (f ∘ e)
  }

instance canonicalBP_Finite [Fintype β] : (canonicalBP F).Finite where
  finite i := inferInstanceAs (Finite (Fin i → β))

theorem canonicalBP_IsOblivious : (canonicalBP F).IsOblivious :=
  fun _ _ _ ↦ rfl

theorem canonicalBP_evalLayer (x : α → β) (i : Fin (Fintype.card α + 1)) :
    (canonicalBP F).evalLayer i x =
      fun (j : Fin i) ↦ x ((Fintype.equivFin α).symm ⟨j, by omega⟩) := by
  induction i using Fin.inductionOn
  · exact funext fun i ↦ Fin.elim0 i
  · rename_i hi
    funext j
    refine j.lastCases ?_ (fun k ↦ ?_)
    · simp [evalLayer, Fin.inductionOn, canonicalBP]
    · simp [evalLayer, Fin.inductionOn, canonicalBP, ← congr_fun hi k]

theorem canonicalBP_computes [Fintype β] : (canonicalBP F).computes F := by
  intro x
  simp only [eval, canonicalBP]
  congr with a
  convert ← congr_fun (canonicalBP_evalLayer F x (Fin.last _)) (Fintype.equivFin α a)
  exact Equiv.apply_symm_apply _ _

theorem canonicalBP_size_eq [Fintype β] :
    (canonicalBP F).size = ∑ i : Fin (Fintype.card α + 1), (Fintype.card β) ^ (i : ℕ) := by
  simp [size, canonicalBP]

/-- Every function can be computed by an oblivious branching program of linear depth and exponential size. -/
theorem computes_linear_depth [Fintype β] :
    ∃ (P : LayeredBranchingProgram α β γ) (_ : P.Finite),
      P.computes F ∧
      P.IsOblivious ∧
      P.depth = Fintype.card α ∧
      P.size = ∑ i : Fin (Fintype.card α + 1), (Fintype.card β) ^ i.val := by
  use canonicalBP F, inferInstance
  and_intros
  · exact canonicalBP_computes F
  · exact canonicalBP_IsOblivious F
  · rfl
  · exact canonicalBP_size_eq F

end canonicalBP
