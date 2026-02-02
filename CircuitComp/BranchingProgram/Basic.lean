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
  /-- The number of layers in the program. We use the convention that `depth = 0` means
  that there is only the input layer; this avoids some awkward issues with `NeZero depth`
  instances or tracking when an index is properly in bounds. -/
  depth : ℕ
  /-- The set of nodes in each layer. -/
  nodes (n : Fin (depth + 1)) : Type v
  /- The variable that each node depends on. -/
  nodeVar {n : Fin depth} : nodes n.castSucc → α
  /- The outgoing edges from each node. -/
  edges {n : Fin depth} : nodes n.castSucc → β → nodes n.succ
  /- The proposition that the starting node is unique.-/
  startUnique : Unique (nodes 0)
  /- The end nodes each return a value in `γ`. -/
  retVals : nodes (Fin.last depth) → γ

/--
An unlayered and unstructured branching program, represented as a DAG.
Compared with `LayeredBranchingProgram`, this allows for infinite branching programs
and input-dependent, unbounded depths.
-/
structure BranchingProgram (α : Type u) (β : Type v) (γ : Type w) where
  nodes : Type v
  start : nodes
  /-- Every node either returns a value in `γ`, or reads a variable `α` and branches to the next node. -/
  info : nodes → γ ⊕ (α × (β → nodes))
  /-- The relation `child` is well-founded, ensuring no infinite paths. -/
  wellFounded : WellFounded (fun v u ↦ ∃ var next val, info u = .inr (var, next) ∧ next val = v)

/-
A `SkipBranchingProgram` is similar to `LayeredBranchingProgram`, but allows for skipping layers:
a node at layer `n` can skip to any layer `m` with `n < m`. This is largely equivalent
computationally, but allows for a reduction in width in some cases.
-/
structure SkipBranchingProgram (α : Type u) (β : Type v) (γ : Type w) where
  depth : ℕ
  nodes (n : Fin (depth + 1)) : Type v
  nodeVar {n : Fin depth} : nodes n.castSucc → α
  edges {n : Fin depth} : nodes n.castSucc → β → Σ (m : Fin (depth + 1)), nodes m
  edges_layer_gt {n : Fin depth} (u : nodes n.castSucc) (b : β) :
    n.castSucc < (edges u b).1
  startUnique : Unique (nodes 0)
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
def evalAt (P : LayeredBranchingProgram α β γ) (x : α → β) (i : Fin P.depth.succ) (u : P.nodes i) : γ :=
  if h : i = Fin.last P.depth then
    P.retVals (h ▸ u)
  else
    let i' : Fin P.depth := i.castPred h
    let u' : P.nodes i'.castSucc := (Fin.castSucc_castPred i h).symm ▸ u
    evalAt P x i'.succ (P.edges u' (x (P.nodeVar u')))
  termination_by P.depth - i
  decreasing_by
    have h_i_lt_depth : i.val < P.depth :=
      lt_of_le_of_ne (Fin.le_last _) (by simpa [Fin.ext_iff] using h)
    have : i.val < (i.castPred h).succ := by simp
    omega

theorem evalAt_castSucc (x : α → β) (i : Fin P.depth) (u : P.nodes i.castSucc) :
    P.evalAt x i.castSucc u = P.evalAt x i.succ (P.edges u (x (P.nodeVar u))) := by
  rw [evalAt]
  simp

/--
`evalAt` starting at the node reached by `evalLayer` yields the same result as `eval`.
-/
@[simp]
theorem evalAt_evalLayer_eq_eval (x : α → β) (i : Fin P.depth.succ) :
    P.evalAt x i (P.evalLayer i x) = P.eval x := by
  induction i using Fin.reverseInduction
  · simp [eval, evalAt]
  · rename_i i ih
    unfold evalAt
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

instance [inst : BPF.Finite] {n} : (BPF n).Finite :=
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

/-- The size of a branching program in a family with bounded width is bounded by width * depth + 1. -/
theorem BPFamily.size_le_bound (hw : BPF.hasWidth (·≤w)) :
    ∀ n, (BPF n).size ≤ w * (BPF n).depth + 1 := by
  intro n
  grw [(BPF n).size_le_width_mul_depth, show (BPF n).width ≤ w from hw n]

/-- If a branching program family has constant width and polynomial depth, it has polynomial size. -/
theorem BPFamily.hasSize_poly_of_width_depth (hw : BPF.hasWidth (·≤w)) (hd : BPF.hasDepth .poly) :
    BPF.hasSize GrowthRate.poly :=
  GrowthRate.mono (GrowthRate.affine_comp hd) (BPF.size_le_bound hw)

end BPFamily

namespace SkipBranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w} (P : SkipBranchingProgram α β γ)

attribute [instance] startUnique

def start : P.nodes 0 :=
  P.startUnique.default

/-- We call a skip branching program finite if the nodes at each layer is finite. -/
protected class Finite : Prop where
  finite : ∀ i, Finite (P.nodes i)

instance [inst : P.Finite] {i} : Finite (P.nodes i) :=
  inst.finite i

/-- We say a branching program is oblivious if all nodes in the same layer read the same variable.
This is often implicit in the "layered" adjective of a layered branching program. -/
def IsOblivious : Prop :=
  ∀ i : Fin P.depth, ∀ j k : P.nodes i.castSucc, P.nodeVar j = P.nodeVar k

/-- Evaluate a `SkipBranchingProgram` starting from a specific node. -/
def evalAt (P : SkipBranchingProgram α β γ) (x : α → β) {i : Fin P.depth.succ} (u : P.nodes i) : γ :=
  if h : i = Fin.last P.depth then
    P.retVals (h ▸ u)
  else
    let i' : Fin P.depth := i.castPred h
    let u' : P.nodes i'.castSucc := (Fin.castSucc_castPred i h).symm ▸ u
    let next := P.edges u' (x (P.nodeVar u'))
    P.evalAt x next.2
  termination_by P.depth - i
  decreasing_by
    simp_wf
    have h_lt : i.val < P.depth := by
      have h_le : i.val ≤ P.depth := by omega
      have h_ne : i.val ≠ P.depth := by
        contrapose! h
        apply Fin.eq_of_val_eq h.1
      omega
    let i' : Fin P.depth := i.castPred h
    let u' : P.nodes i'.castSucc := (Fin.castSucc_castPred i h).symm ▸ u
    have h_gt := P.edges_layer_gt u' (x (P.nodeVar u'))
    simp only [i', u'] at h_gt
    apply Nat.sub_lt_sub_left h_lt h_gt

theorem evalAt_castSucc (x : α → β) (i : Fin P.depth) (u : P.nodes i.castSucc) :
    P.evalAt x u = P.evalAt x (P.edges u (x (P.nodeVar u))).2 := by
  rw [evalAt]
  simp

/-- Evaluate a `SkipBranchingProgram` on inputs `x`. -/
def eval (x : α → β) : γ :=
  P.evalAt x P.start

/--
If a SkipBranchingProgram has depth > 0, then α must be nonempty because the start node
at layer 0 must read a variable.
-/
theorem nonempty_of_depth_pos (h : 0 < P.depth) : Nonempty α :=
  let z : Fin P.depth := ⟨0, h⟩
  let u : P.nodes z.castSucc := cast (by simp [z]) P.start
  ⟨P.nodeVar u⟩

/-- The "active nodes" ahead of layer `i` are the nodes with an edge going past layer `i` there. -/
def ActiveNodes (i : Fin (P.depth + 1)) : Type v :=
  { u : (m : Fin (P.depth + 1)) × P.nodes m // u.1 > i ∧ ∃ l₂ : Fin (P.depth),
    l₂.castSucc < i ∧ ∃ (v : P.nodes l₂.castSucc) (b : β), P.edges v b = u }

lemma ActiveNodes_last_isEmpty : IsEmpty (P.ActiveNodes (Fin.last P.depth)) :=
  ⟨fun ⟨_, h, _⟩ ↦ (Fin.le_last _).not_gt h⟩

/-- The width of a `SkipBranchingProgram` is not the count of nodes at each layer (since this could
be made 1 without much difficulty, by increasing depth), but the count of nodes *and* the edges passing
that layer by - this reflects the notion of width most naturally corresponding to
`LayeredBranchingProgram.width`, and is the quantity preserved by `SkipBranchingProgram.toLayered`. -/
def width : ℕ :=
  ⨆ i : Fin (P.depth + 1), Nat.card (P.ActiveNodes i)

end SkipBranchingProgram

namespace BranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w}
variable (P : BranchingProgram α β γ)

/-- Evaluation for `BranchingProgram` starting from a specific node. -/
def evalAt (x : α → β) (u : P.nodes) : γ :=
  P.wellFounded.fix (fun u ih ↦
    match h : P.info u with
    | .inl res => res
    | .inr (var, next) => ih (next (x var)) ⟨var, next, x var, h, rfl⟩
  ) u

/-- Evaluation for `BranchingProgram`. -/
def eval (x : α → β) : γ :=
  P.evalAt x P.start

section height

open Classical
variable [Fintype P.nodes]

/-- The height of a node in a branching program is the length of the longest path to a leaf. -/
noncomputable def height (u : P.nodes) : ℕ :=
  letI := Fintype.ofFinite P.nodes
  P.wellFounded.fix (fun u ih ↦
    match h : P.info u with
    | .inl _ => 0
    | .inr (var, next) =>
      let children := Finset.univ.filter (fun v ↦ ∃ b, next b = v)
      1 + children.attach.sup (fun (v : {x // x ∈ children}) ↦
          ih v.1 (by
            have hv := v.2
            rw [Finset.mem_filter] at hv
            rcases hv with ⟨_, ⟨b, hb⟩⟩
            exact ⟨var, next, b, h, hb⟩
          )
      )
  ) u

/-- The depth of a branching program is the height of the start node. -/
noncomputable def depth : ℕ :=
  P.height P.start

theorem height_eq_zero_of_leaf (u : P.nodes) (res : γ)
    (h : P.info u = .inl res) : P.height u = 0 := by
  grind [WellFounded.fix_eq, height]

theorem height_eq_succ_sup (u : P.nodes) (var : α) (next : β → P.nodes) (h : P.info u = .inr (var, next)) :
    P.height u = 1 + (Finset.univ.filter (fun v ↦ ∃ b, next b = v)).sup (fun v ↦ P.height v) := by
  rw [height, WellFounded.fix_eq]
  simp only [Finset.sup_attach]
  rw [h]
  convert rfl

theorem height_pos (u : P.nodes) (var : α) (next : β → P.nodes) (h : P.info u = .inr (var, next)) :
    0 < P.height u := by
  have h_height_def : P.height u = 1 + (Finset.univ.filter (fun v ↦ ∃ b, next b = v)).sup (fun v ↦ P.height v) := by
    exact height_eq_succ_sup P u var next h;
  exact h_height_def.symm ▸ add_pos_of_pos_of_nonneg zero_lt_one ( Nat.zero_le _ )

theorem is_internal_of_height_pos (u : P.nodes)
    (h : 0 < P.height u) : ∃ var next, P.info u = .inr (var, next) := by
  rcases h : P.info u with (_  | ⟨_, _⟩)
  · have := height_eq_zero_of_leaf P _ _ h
    linarith
  · simp

theorem is_leaf_of_height_zero (u : P.nodes)
    (h : P.height u = 0) : ∃ res, P.info u = .inl res := by
  by_contra h_contra;
  have h_height_pos : 0 < P.height u := by
    -- Since u is not a leaf, its info is .inr (var, next).
    obtain ⟨var, next, h_info⟩ : ∃ var next, P.info u = .inr (var, next) := by
      cases h : P.info u <;> tauto;
    convert P.height_pos u var next h_info
  grind

theorem height_child_lt (u : P.nodes) (var : α) (next : β → P.nodes) (h : P.info u = .inr (var, next)) (b : β) :
    P.height (next b) < P.height u := by
  rw [height_eq_succ_sup P u var next h, add_comm, Nat.lt_add_one_iff]
  exact Finset.le_sup (by simp)

theorem leaf_of_layer_eq_depth (u : P.nodes) (h : P.height u = P.depth - P.depth) :
    ∃ res, P.info u = .inl res :=
  P.is_leaf_of_height_zero u (by omega)

end height

section rel
open Relation

def adj (u v : P.nodes) : Prop :=
  ∃ var next, P.info u = .inr (var, next) ∧ ∃ b, next b = v

def Reachable (u : P.nodes) : Prop :=
  ReflTransGen P.adj P.start u

variable [Fintype P.nodes]

theorem height_lt_of_adj {u v : P.nodes}
    (h : P.adj u v) : P.height v < P.height u := by
  rcases h with ⟨var, next, hx, b, rfl⟩;
  convert BranchingProgram.height_child_lt P u var next hx b

theorem height_le_of_reachable {u : P.nodes}
    (h : P.Reachable u) : P.height u ≤ P.height P.start := by
  cases h ; aesop;
  rename_i b hb₁ hb₂;
  have h_adj_anti : ∀ c d : P.nodes, P.adj c d → P.height d < P.height c := by
    intro c d hcd
    obtain ⟨var, next, hinfo, ⟨b, hb⟩⟩ := hcd
    have h_height_lt : P.height (next b) < P.height c := by
      convert P.height_child_lt c var next hinfo b using 1
    aesop;
  have h_adj_anti : ∀ c d : P.nodes, ReflTransGen P.adj c d → P.height d ≤ P.height c := by
    intro c d hcd; induction hcd <;> [ rfl; linarith [ h_adj_anti _ _ ‹_› ] ] ;
  exact le_trans ( h_adj_anti _ _ ( ReflTransGen.single hb₂ ) ) ( h_adj_anti _ _ hb₁ )

theorem eq_start_of_reachable_and_height_eq {u : P.nodes}
    (h : P.Reachable u) (heq : P.height u = P.height P.start) : u = P.start := by
  have h_height_u : u ≠ P.start → P.height u < P.height P.start := by
    intro hu
    have h_height_u : ∀ v : P.nodes, P.Reachable v → v ≠ P.start → P.height v < P.height P.start := by
      intro w hw hw_ne_start
      induction hw
      · contradiction
      · have _ := height_lt_of_adj P ‹_›
        grind
    exact h_height_u u h hu;
  exact Classical.not_not.1 fun h' => heq.not_lt <| h_height_u h'

end rel
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
`evalAt` on the converted DAG equals `evalAt` on the layered program.
-/
theorem toBranchingProgram_evalAt_eq_evalAt (x : α → β) (i : Fin L.depth.succ) (u : L.nodes i) :
    L.toBranchingProgram.evalAt x ⟨i, u⟩ = L.evalAt x i u := by
  induction' i using Fin.reverseInduction with i ih;
  · rw [ evalAt ];
    unfold BranchingProgram.evalAt;
    rw [ WellFounded.fix_eq ];
    unfold toBranchingProgram; aesop;
  · unfold BranchingProgram.evalAt evalAt
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
  convert ← toBranchingProgram_evalAt_eq_evalAt L x 0 L.start
  exact evalAt_evalLayer_eq_eval L x 0

end LayeredBranchingProgram

namespace BranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w} (P : BranchingProgram α β γ) [Fintype P.nodes]

/--
Conversion from `BranchingProgram` to `SkipBranchingProgram`.
Restricts nodes to those reachable from the start node.
-/
def toSkip : SkipBranchingProgram α β γ where
  depth := P.depth
  nodes := fun i ↦ { u : P.nodes // P.height u = P.depth - i ∧ P.Reachable u }
  nodeVar := fun {i} ⟨u, hu⟩ ↦
    match h : P.info u with
    | .inl _ => Classical.choice (by
    -- Since there's a path from u to v, there must be at least one variable in α that's involved in the edges of the path.
    have h_var : ∃ var : α, ∃ next : β → P.nodes, P.info u = Sum.inr (var, next) := by
      have h_var : 0 < P.height u := by
        rw [ hu.1 ];
        exact Nat.sub_pos_of_lt ( Fin.is_lt i );
      exact is_internal_of_height_pos P u h_var;
    exact ⟨ h_var.choose ⟩)
    | .inr (var, _) => var
  edges := fun {i} ⟨u, hu⟩ b ↦
    match h : P.info u with
    | .inl _ => Classical.choice (by
    exact ⟨ ⟨ i.castSucc, u, hu ⟩ ⟩)
    | .inr (var, next) =>
        let v := next b
        let hv := P.height v
        let j := P.depth - hv
        ⟨⟨j, by
          exact Nat.lt_succ_of_le ( Nat.sub_le _ _ )⟩, ⟨v, by
          -- Since $v$ is reachable from $u$ and $u$ is reachable from the start, $v$ is reachable from the start.
          have hv_reachable : P.Reachable v := by
            exact hu.2.tail ( by exact ⟨ var, next, h, b, rfl ⟩ );
          exact ⟨ by rw [ Nat.sub_sub_self ( show hv ≤ P.depth from P.height_le_of_reachable hv_reachable ) ], hv_reachable ⟩⟩⟩
  edges_layer_gt := fun {i} ⟨u, hu⟩ b ↦ by
    by_cases h : ∃ var next, P.info u = .inr (var, next);
    · rcases h with ⟨ var, next, h ⟩;
      convert Nat.lt_sub_of_add_lt _;
      rotate_left;
      exact P.height ( next b );
      exact 0;
      exact P.depth - i.castSucc;
      · exact lt_of_lt_of_le ( BranchingProgram.height_child_lt _ _ _ _ h _ ) ( by omega );
      · grind;
    · cases h' : P.info u <;> simp_all +decide;
      · have := hu.1 ▸ BranchingProgram.height_eq_zero_of_leaf P u _ h'; simp_all +decide ;
        exact absurd this ( Nat.sub_ne_zero_of_lt ( Fin.is_lt i ) );
      · exact False.elim <| h _ _ rfl
  startUnique := {
    default := ⟨P.start, by simp [depth, Reachable]; rfl⟩
    uniq := fun ⟨u, hu⟩ ↦ by
      exact Subtype.ext <| eq_start_of_reachable_and_height_eq P hu.2 <| by simpa using hu.1;
  }
  retVals := fun ⟨u, hu⟩ ↦
    match h : P.info u with
    | .inl res => res
    | .inr _ => Classical.choice (by
    -- Since the branching program must return a value in γ when it reaches a leaf node, γ cannot be empty.
    have h_nonempty : ∃ x : P.nodes, ∃ res : γ, P.info x = .inl res := by
      have h_nonempty : ∃ x : P.nodes, P.height x = 0 := by
        exact ⟨ u, hu.1.trans ( Nat.sub_self _ ) ⟩;
      exact h_nonempty.elim fun x hx => by obtain ⟨ res, hres ⟩ := BranchingProgram.is_leaf_of_height_zero P x hx; exact ⟨ x, res, hres ⟩ ;
    exact ⟨ h_nonempty.choose_spec.choose ⟩)

@[simp]
theorem toSkip_depth : P.toSkip.depth = P.depth :=
  rfl

@[simp]
theorem toSkip_start :
    P.toSkip.start.val = P.start :=
  rfl

theorem toSkip_evalAt
    (x : α → β) (i : Fin P.depth.succ) (u : P.toSkip.nodes i) :
    P.toSkip.evalAt x u = P.evalAt x u.1 := by
  induction' n : P.toSkip.depth - i.val using Nat.strong_induction_on with n ih generalizing i u;
  unfold SkipBranchingProgram.evalAt
  split_ifs with h;
  · unfold evalAt;
    have h_layer : P.height u.val = P.depth - i := by
      exact u.2.1;
    have h_leaf : ∃ res, P.info u.val = .inl res := by
      convert leaf_of_layer_eq_depth P u.val _;
      rw [ h_layer, h, Fin.val_last, toSkip_depth ];
    rw [ WellFounded.fix_eq ];
    unfold toSkip; aesop;
  · convert ih _ _ _ _ rfl using 1;
    · sorry
    · rw [ ← n ];
      apply Nat.sub_lt_sub_left
      · exact lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using h );
      · convert P.toSkip.edges_layer_gt _ _;
        rotate_left;
        exact Fin.castPred i h;
        exact ⟨ u.1, by simpa [ Fin.castSucc_castPred ] using u.2 ⟩;
        exact x ( P.toSkip.nodeVar ( Fin.castSucc_castPred i h ▸ u ) );
        exact Fin.val_fin_lt

/--
The conversion from BranchingProgram to SkipBranchingProgram preserves semantics (eval).
-/
@[simp]
theorem toSkip_eval : P.toSkip.eval = P.eval := by
  ext1
  rw [SkipBranchingProgram.eval, eval, toSkip_evalAt, toSkip_start]

end BranchingProgram

namespace SkipBranchingProgram
open Classical

variable {α : Type u} {β : Type v} {γ : Type w} (P : SkipBranchingProgram α β γ)

def toLayered : LayeredBranchingProgram α β γ where
  depth := P.depth
  nodes i := P.nodes i ⊕ P.ActiveNodes i
  nodeVar {i} u := match u with
    | .inl u => P.nodeVar u
    | .inr _ =>
      if h : Nonempty (P.nodes i.castSucc) then
        P.nodeVar h.some
      else
        (P.nonempty_of_depth_pos (lt_of_le_of_lt (Nat.zero_le _) i.isLt)).some
  edges {i} node val := match node with
    | .inl u =>
      let next := P.edges u val
      let m := next.1
      let v := next.2
      if h : m = i.succ then
        .inl (h ▸ v)
      else
        .inr ⟨⟨m, v⟩,
          ⟨lt_of_le_of_ne' (P.edges_layer_gt u val) h, ⟨i, i.castSucc_lt_succ, u, val, rfl⟩⟩⟩
    | .inr ⟨⟨m, v⟩, hl, hr⟩ =>
      if h : m = i.succ then
        .inl (h ▸ v)
      else
        .inr ⟨⟨m, v⟩,
          ⟨lt_of_le_of_ne' (Nat.succ_le_of_lt hl) h, hr.imp fun _ ⟨h₁, h₂⟩ ↦ ⟨Nat.lt_succ_of_lt h₁, h₂⟩⟩⟩
  startUnique := {
    default := .inl P.start
    uniq u := by
      rcases u with _ | ⟨_, h⟩
      · simpa using P.startUnique.uniq _
      · simp at h
  }
  retVals u := match u with
    | .inl u => P.retVals u
    | .inr u => (P.ActiveNodes_last_isEmpty.false u).elim

/--
The `evalAt` function on the converted layered branching program agrees with the `evalAt` on the original skip branching program.
-/
theorem toLayered_evalAt (x : α → β) (i : Fin (P.depth + 1)) (node : P.toLayered.nodes i) :
    (P.toLayered).evalAt x i node =
      match node with
      | .inl u => P.evalAt x u
      | .inr ⟨⟨_, v⟩, _⟩ => P.evalAt x v := by
  revert node
  induction' i using Fin.reverseInduction with i ih
  · rintro (_ | ⟨v, h⟩)
    · simp [LayeredBranchingProgram.evalAt, toLayered]
      unfold evalAt
      aesop
    · exact absurd h.1 (v.1.le_last).not_gt
  · intro node
    rw [LayeredBranchingProgram.evalAt_castSucc]
    convert ih _ using 1
    rcases node with (v | ⟨_, h₁⟩)
    · simp [toLayered]
      split_ifs with h <;> simp [*]
      · convert evalAt_castSucc P x i v
        · exact h.symm
        · exact eqRec_heq _ _
      · apply evalAt_castSucc
    · simp [toLayered]
      grind

/--
The converted layered branching program computes the same function as the original skip branching program.
-/
@[simp]
theorem toLayered_eval : P.toLayered.eval = P.eval := by
  ext x
  rw [← P.toLayered.evalAt_evalLayer_eq_eval x 0]
  exact P.toLayered_evalAt x 0 (Sum.inl P.start)

end SkipBranchingProgram
