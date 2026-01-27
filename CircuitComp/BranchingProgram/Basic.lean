import CircuitComp.FuncFamily
import CircuitComp.GrowthRate

import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

universe u v w

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

def computes (F : (α → β) → γ) : Prop :=
  ∀ x, P.eval x = F x

/--
Evaluation for `LayeredBranchingProgram` starting from a specific layer and node.
-/
def evalFrom (P : LayeredBranchingProgram α β γ) (x : α → β) (i : Fin P.depth.succ) (u : P.nodes i) : γ :=
  if h : i = Fin.last P.depth then
    P.retVals (h ▸ u)
  else
    let i' : Fin P.depth := i.castPred h
    let u' : P.nodes i'.castSucc := (Fin.castSucc_castPred i h).symm ▸ u
    evalFrom P x i'.succ (P.edges u' (x (P.nodeVar u')))
  termination_by P.depth - i
  decreasing_by
    have h_i_lt_depth : i.val < P.depth :=
      lt_of_le_of_ne (Fin.le_last _) (by simpa [Fin.ext_iff] using h)
    have : i.val < (i.castPred h).succ := by simp
    omega

/--
`evalFrom` starting at the node reached by `evalLayer` yields the same result as `eval`.
-/
@[simp]
theorem evalFrom_evalLayer_eq_eval (x : α → β) (i : Fin P.depth.succ) :
    P.evalFrom x i (P.evalLayer i x) = P.eval x := by
  induction i using Fin.reverseInduction
  · simp [eval, evalFrom]
  · rename_i i ih
    unfold evalFrom
    simpa using ih

end LayeredBranchingProgram

section BPFamily

/-- A `BPFamily` is a collection of `LayeredBranchingProgram`s parameterized by an input size `n`.
The `n`th program must have input type `Fin n` (variables), read values of type `α`, and output `α`. -/
def BPFamily (α : Type u) := (n : ℕ) → LayeredBranchingProgram (Fin n) α α

variable {α : Type u} (BPF : BPFamily α)

/-- A `BPFamily` `computes` a function family if that is given by its `eval`.-/
def BPFamily.computes (F : FuncFamily₁ α) : Prop :=
  ∀ n, (BPF n).eval = F n

/-- Predicate expressing that the depth grows as O(f n). -/
def BPFamily.hasDepth (f : GrowthRate) : Prop :=
  (fun n ↦ (BPF n).depth) ∈ f

/-- Predicate expressing that the width is bounded by `w`. For expressing a particular constant width
such as 3, the GrowthRate can be provided as `{ 3 }` or `{ fun _ ↦ 3 }`, note that this is not a
`LawfulGrowthRate` (since it is not closed under addition). -/
def BPFamily.hasWidth (w : GrowthRate) : Prop :=
  (fun n ↦ (BPF n).width) ∈ w

/-- Predicate expressing that all programs in the family are finite. -/
protected class BPFamily.Finite : Prop where
  finite : ∀ n, (BPF n).Finite

instance [inst : BPFamily.Finite BPF] {n} : (BPF n).Finite :=
  inst.finite n

/-- Predicate expressing that the size grows as O(f n). -/
def BPFamily.hasSize (f : GrowthRate) : Prop :=
  (fun n ↦ (BPF n).size) ∈ f

/-- Predicate expressing that the programs are oblivious. -/
def BPFamily.IsOblivious : Prop :=
  ∀ n, (BPF n).IsOblivious

/-- A `BPClass` is a set of function families defined by branching programs with
a bound on depth and a bound on width. Optionally, we can require that the programs are
oblivious. -/
def BPClass (width : GrowthRate) (depth : GrowthRate) (obliv : Bool) : Set (FuncFamily₁ α) :=
  fun fs ↦ ∃ (BPF : BPFamily α) (_ : BPF.Finite),
    BPF.computes fs
    ∧ BPF.hasWidth width
    ∧ BPF.hasDepth depth
    ∧ (obliv → BPF.IsOblivious)

variable [BPF.Finite] {w : ℕ}
/--
The size of a branching program in a family with bounded width is bounded by width * depth + 1.
-/
theorem BPFamily.size_le_bound (hw : BPF.hasWidth (·≤w)) :
    ∀ n, (BPF n).size ≤ w * (BPF n).depth + 1 := by
  intro n
  grw [(BPF n).size_le_width_mul_depth, show (BPF n).width ≤ w from hw n]

/--
If a branching program family has constant width and polynomial depth, it has polynomial size.
-/
theorem BPFamily.hasSize_poly_of_width_depth (hw : BPF.hasWidth (·≤w)) (hd : BPF.hasDepth .poly) :
    BPF.hasSize GrowthRate.poly :=
  GrowthRate.mono (GrowthRate.affine_comp hd) (BPF.size_le_bound hw)

end BPFamily

/--
An unlayered and unstructured branching program, represented as a DAG.
Compared with `LayeredBranchingProgram`, this allows for infinite branching programs
and input-dependent, unbounded depths.
-/
structure BranchingProgram (α : Type u) (β : Type v) (γ : Type w) where
  nodes : Type v
  start : nodes
  info : nodes → Sum γ (α × (β → nodes))
  /-- The relation `child` is well-founded, ensuring no infinite paths. -/
  wellFounded : WellFounded (fun v u ↦ ∃ var next val, info u = .inr (var, next) ∧ next val = v)

namespace BranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w}
variable (P : BranchingProgram α β γ)

/--
Evaluation for `BranchingProgram` starting from a specific node.
-/
def evalAt (x : α → β) (u : P.nodes) : γ :=
  P.wellFounded.fix (fun u ih ↦
    match h : P.info u with
    | .inl res => res
    | .inr (var, next) => ih (next (x var)) ⟨var, next, x var, h, rfl⟩
  ) u

/--
Evaluation for `BranchingProgram`.
-/
def eval (x : α → β) : γ :=
  P.evalAt x P.start

end BranchingProgram

namespace LayeredBranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w} (L : LayeredBranchingProgram α β γ)

/--
Conversion from `LayeredBranchingProgram` to `BranchingProgram`.
-/
def toBranchingProgram : BranchingProgram α β γ where
  nodes := Sigma L.nodes
  start := ⟨0, L.start⟩
  info := fun ⟨i, u⟩ ↦
    i.lastCases
      (fun u ↦ .inl (L.retVals u))
      (fun j u ↦ .inr (L.nodeVar u, fun b ↦ ⟨j.succ, L.edges u b⟩))
      u
  wellFounded := by
    refine ⟨fun v ↦ ?_⟩
    rcases v with ⟨i, u⟩
    induction i using Fin.reverseInduction
    · constructor
      simp [Fin.lastCases]
    · rename_i ih
      simp [Fin.lastCases] at ih ⊢
      constructor
      rintro v ⟨var, next, h₁, x, rfl⟩
      simp at h₁
      rw [← h₁.2]
      exact ih (L.edges u x)

/--
`evalAt` on the converted DAG equals `evalFrom` on the layered program.
-/
theorem toBranchingProgram_evalAt_eq_evalFrom (x : α → β) (i : Fin L.depth.succ) (u : L.nodes i) :
    L.toBranchingProgram.evalAt x ⟨i, u⟩ = L.evalFrom x i u := by
  induction' i using Fin.reverseInduction with i ih;
  · rw [ evalFrom ];
    unfold BranchingProgram.evalAt;
    rw [ WellFounded.fix_eq ];
    unfold toBranchingProgram; aesop;
  · unfold BranchingProgram.evalAt evalFrom
    convert ih (L.edges u (x (L.nodeVar u))) using 1
    · rw [BranchingProgram.evalAt, WellFounded.fix_eq]
      simp [toBranchingProgram, Fin.lastCases]
      rw [Fin.reverseInduction_castSucc]
    · simp

/-
The DAG conversion `LayeredBranchingProgram.toBranchingProgram` preserves semantics.
-/
@[simp]
theorem toBranchingProgram_eval : L.toBranchingProgram.eval = L.eval := by
  funext x
  convert ← toBranchingProgram_evalAt_eq_evalFrom L x 0 L.start
  exact evalFrom_evalLayer_eq_eval L x 0

end LayeredBranchingProgram
