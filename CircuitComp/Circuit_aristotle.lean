/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 50e718a3-20df-4145-8e51-e22fa3978aac

The following was proved by Aristotle:

- theorem FeedForward.evalNode_comp_right {α : Type u} {a b c : Type v}
    (F : FeedForward α a b) (G : FeedForward α b c)
    (j : Fin (G.depth + 1)) (node : G.nodes j) (x : a → α) :
    let k : Fin (F.depth + G.depth + 1)

- theorem eval_sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂) (hf : f.depth = d) (hg : g.depth = d) :
    ∀ (x : a ⊕ a₂ → α), (f.sum g hf hg).eval x = Sum.elim (f.eval (x ∘ .inl)) (g.eval (x ∘ .inr))
-/

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
  nodes_zero : nodes 0 = inp
  nodes_last : nodes (Fin.last depth) = out

namespace FeedForward

attribute [simp] nodes_zero

attribute [simp] nodes_last

variable {α : Type u} {inp out a b c a₂ b₂ : Type v} (F : FeedForward α inp out)

/-- The identity GateOp. -/
abbrev GateOp.id (α : Type u) : GateOp α where
  ι := PUnit
  func x := x .unit

variable {F} in
theorem inp_eq_out_of_depth_zero (h : F.depth = 0) : inp = out :=
  (F.nodes_zero.symm.trans (congrArg _ <| Fin.zero_eq_last_iff.mpr h)).trans F.nodes_last

def Gate.eval {domain : Type*} (g : FeedForward.Gate α domain) (xs : domain → α) : α :=
  g.op.func (xs <| g.inputs ·)

/-- Evaluate a `FeedForward` on some input data and get a particular node's value -/
def evalNode {d : Fin (F.depth + 1)} (node : F.nodes d) (xs : inp → α) : α :=
  let ⟨d, hd⟩ := d
  Nat.recAux (fun _ node' ↦ xs (F.nodes_zero ▸ node'))
    (fun n ih hd node₀ ↦
      (F.gates ⟨n, Nat.succ_lt_succ_iff.mp hd⟩ node₀).eval (ih _)) d hd node

/- Generated from:
rcases d with ⟨d, hd⟩
induction d
· exact xs (F.nodes_zero ▸ node)
· rename_i d' ih
  apply (F.gates ⟨d', Nat.succ_lt_succ_iff.mp hd⟩ node).eval
  exact fun node' ↦ ih (Nat.lt_of_succ_lt hd) node'
-/

/-- Evaluate a `FeedForward` on some input data. Gives a value for each node at the last layer. -/
def eval (xs : inp → α) : out → α :=
  fun n ↦ F.evalNode (d := (Fin.last F.depth)) (F.nodes_last.symm.rec n) xs

/-- Evaluate a `FeedForward` on some input data, and get the unique output. -/
def eval₁ [Unique out] (xs : inp → α) : α :=
  F.eval xs default

/-- Relabel the input type of a `FeedForward` given an `Equiv`. -/
def relabelIn (hF : F.depth ≠ 0) (e : inp ≃ a) : FeedForward α a out :=
  have : NeZero F.depth := ⟨hF⟩
  { depth := F.depth
    nodes k := if k = 0 then a else F.nodes k
    gates k n := if hk : k = 0 then
        have g := F.gates k n
        ⟨g.op, have gi := g.inputs; by simp [hk] at gi ⊢; exact ⇑e ∘ gi⟩
      else cast (by simp [hk]) (F.gates k n)
    nodes_zero := by simp
    nodes_last := by simp [hF]
  }

--TODO pull out to Mathlib
theorem Fin.castSucc_lt_top (n : ℕ) (x : Fin n) : x.castSucc < ⊤ :=
  Ne.lt_top (by simp [Fin.ext_iff, x.2.ne])

-- /-- Relabel the output type of a `FeedForward` given an `Equiv`. -/
-- def relabelOut (hF : F.depth ≠ 0) (e : out ≃ a) : FeedForward α inp a :=
--   have : NeZero F.depth := ⟨hF⟩
--   { depth := F.depth
--     nodes k := if k = ⊤ then a else F.nodes k
--     gates k n := if hk : k = ⊤ then
--         have g := F.gates k (by simp [Fin.top_eq_last, hk] at n ⊢; exact e.symm n)
--         ⟨g.op, have gi := g.inputs; fun i ↦ by simp [hk, Fin.top_eq_last, Fin.castSucc] at gi ⊢; exact sorry⟩
--       else cast (by simp [Fin.top_eq_last, (Fin.castSucc_lt_last k).ne]) (F.gates k sorry)
--     nodes_zero := by simp [hF]
--     nodes_last := by simp [Fin.top_eq_last]
--   }

/-- Compose two `FeedForward`s by stacking one on top of the other. -/
def comp {a b c : Type v} (g : FeedForward α b c) (f : FeedForward α a b) : FeedForward α a c where
  depth := f.depth + g.depth
  nodes k := if h : k.val ≤ f.depth then f.nodes ⟨k, by omega⟩ else g.nodes ⟨k - f.depth, by omega⟩
  gates k n := if h : k.val < f.depth
    then cast
      (by rw [dif_pos (by exact Nat.le_of_succ_le h)]; rfl)
      (f.gates ⟨k.val, h⟩ (cast (by rw [dif_pos (by exact h)]; simp) n))
    else cast
      (by
        split_ifs with h₂
        · congr 1
          trans b
          · convert g.nodes_zero
            ext
            simp at h₂ ⊢
            omega
          · convert f.nodes_last.symm using 2
            ext
            simp at h₂ ⊢
            omega
        · rfl)
      (g.gates ⟨k.val - f.depth, by omega⟩
        (cast (by rw [dif_neg (by simp; omega)]; congr; simp; omega) n))
  nodes_zero := by simp
  nodes_last := by
    split_ifs with h
    · replace h : g.depth = 0 := by simpa using h
      refine Eq.trans ?_ (g.inp_eq_out_of_depth_zero h)
      simpa [-FeedForward.nodes_last, h] using f.nodes_last
    · simpa [-FeedForward.nodes_last] using g.nodes_last

/-
Helper lemma: The evaluation of a node in the first part of a composed circuit `G.comp F` is the same as its evaluation in `F`.
-/
theorem FeedForward.evalNode_comp_left {α : Type u} {a b c : Type v}
    (F : FeedForward α a b) (G : FeedForward α b c)
    (i : Fin (F.depth + 1)) (node : F.nodes i) (x : a → α) :
    let k : Fin (F.depth + G.depth + 1) := ⟨i.val, by
      linarith [ Fin.is_lt i ]⟩
    (G.comp F).evalNode (d := k) (cast (by
      exact Eq.symm (show (G.comp F).nodes k = F.nodes i by simp +zetaDelta [comp]; intro h; linarith [Fin.is_lt i])) node) x = F.evalNode node x := by
  all_goals generalize_proofs at *;
  simp_all +decide [ FeedForward.evalNode, FeedForward.comp ];
  rw [ Nat.recAux, Nat.recAux ];
  induction i using Fin.inductionOn <;> simp +decide [ * ];
  · grind;
  · unfold FeedForward.Gate.eval at *
    simp_all only [Fin.coe_castSucc, Fin.val_succ]
    rename_i pf pf_1 a_1 pf_2
    unfold FeedForward.comp at *
    simp_all [↓reduceDIte]
    split at pf_2
    · congr!;
      · grind +ring;
      · convert a_1 _ _ _;
        grind;
        exact Nat.lt_of_succ_lt pf;
        exact rfl;
    · grind

/-
Helper lemma: The evaluation of a node in the second part of a composed circuit `G.comp F` is the same as its evaluation in `G` given the output of `F`.
-/
theorem FeedForward.evalNode_comp_right {α : Type u} {a b c : Type v}
    (F : FeedForward α a b) (G : FeedForward α b c)
    (j : Fin (G.depth + 1)) (node : G.nodes j) (x : a → α) :
    let k : Fin (F.depth + G.depth + 1) := ⟨F.depth + j.val, by
      linarith [ Fin.is_lt j ]⟩
    (G.comp F).evalNode (d := k) (cast (by
    -- By definition of `G.comp F`, the nodes at position `k` are the same as the nodes at position `j` in `G`.
    simp [FeedForward.comp, k];
    cases F ; aesop) node) x = G.evalNode node (F.eval x) := by
  simp +decide [ add_assoc, add_comm, add_left_comm, FeedForward.comp ] at *;
  split_ifs at * <;> simp_all +decide [ Nat.succ_eq_add_one, add_lt_add_iff_left ];
  · subst_vars;
    convert FeedForward.evalNode_comp_left F G ( Fin.last F.depth ) _ _ using 1;
    congr!;
    grind;
  ·
    -- By definition of `evalNode`, we can split into cases based on the value of `i`. Since `j` is not zero, we have `j > 0`.
    have h_pos : 0 < j.val := by
      exact Nat.pos_of_ne_zero fun h => ‹¬j = 0› <| Fin.ext h;
    set k : Fin (F.depth + G.depth + 1) := ⟨F.depth + j.val, by
      linarith [ Fin.is_lt j ]⟩
    generalize_proofs at *;
    linarith

@[simp]
theorem eval_comp (F : FeedForward α a b) (G : FeedForward α b c) : (G.comp F).eval = G.eval ∘ F.eval := by
  funext x
  funext n
  simp [FeedForward.eval]
  convert FeedForward.evalNode_comp_right F G ( Fin.last G.depth ) _ _;
  grind

/-- Run two `FeedForward`s in "parallel" on separate inputs of equal depth . -/
def sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂) (hf : f.depth = d) (hg : g.depth = d) :
    FeedForward α (a ⊕ a₂) (b ⊕ b₂) where
  depth := d
  nodes k := f.nodes (k.cast (by rw [hf])) ⊕ g.nodes (k.cast (by rw [hg]))
  gates k :=
    Sum.elim
      (fun n ↦
        have := f.gates (k.cast (by rw [hf])) (cast (by simp) n)
        ⟨this.op, .inl ∘ this.inputs⟩)
      (fun n ↦
        have := g.gates (k.cast (by rw [hg])) (cast (by simp) n)
        ⟨this.op, .inr ∘ this.inputs⟩)
  nodes_zero := by simp
  nodes_last := by simp

noncomputable section AristotleLemmas

theorem evalNode_sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂) (hf : f.depth = d) (hg : g.depth = d)
    (k : Fin (d + 1)) (node : (f.sum g hf hg).nodes k) (x : a ⊕ a₂ → α) :
    (f.sum g hf hg).evalNode node x =
      Sum.elim (fun n => f.evalNode n (x ∘ Sum.inl)) (fun n => g.evalNode n (x ∘ Sum.inr)) node := by
        revert k node;
        intro k n;
        induction k using Fin.inductionOn
        all_goals generalize_proofs at *;
        · cases n <;> simp +decide [ FeedForward.evalNode ];
          · cases f ; cases g ; aesop;
          · cases f ; cases g ; aesop;
        · unfold FeedForward.evalNode;
          cases n <;> simp ( config := { decide := Bool.true } ) [ *, Nat.recAux ];
          · unfold FeedForward.Gate.eval;
            congr! 1;
            aesop;
          · unfold FeedForward.Gate.eval;
            congr! 2;
            aesop

theorem cast_Sum_inl {α α' β β' : Type} (hα : α = α') (hβ : β = β') (a : α) :
    cast (congr (congrArg Sum hα) hβ) (Sum.inl a) = Sum.inl (cast hα a) := by
  cases hα; cases hβ; rfl

theorem cast_Sum_inr {α α' β β' : Type} (hα : α = α') (hβ : β = β') (b : β) :
    cast (congr (congrArg Sum hα) hβ) (Sum.inr b) = Sum.inr (cast hβ b) := by
  cases hα; cases hβ; rfl

end AristotleLemmas

theorem eval_sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂) (hf : f.depth = d) (hg : g.depth = d) :
    ∀ (x : a ⊕ a₂ → α), (f.sum g hf hg).eval x = Sum.elim (f.eval (x ∘ .inl)) (g.eval (x ∘ .inr)) := by
  intro x
  ext n;
  unfold FeedForward.eval;
  convert FeedForward.evalNode_sum f g hf hg ( Fin.last d ) ( ?_ ) x using 2;
  simp +decide [ Fin.cast, f.nodes_last, g.nodes_last ];
  congr;
  · have h_last : f.nodes (Fin.last f.depth) = b := by
      exact f.nodes_last;
    exact h_last.symm.trans ( by congr; aesop );
  · have := g.nodes_last;
    exact this.symm.trans ( by congr; aesop );
  · congr! 3;
    · convert f.nodes_last.symm;
      aesop;
    · bound;
  · congr! 2;
    · exact hg ▸ g.nodes_last.symm;
    · aesop;
    · grind;
  · grind

/-- The cardinal width of a feedforward circuit is the largest number of nodes in any layer. -/
noncomputable def width_card : Cardinal :=
  ⨆ d, Cardinal.mk (F.nodes d)

/-- The size of a feedforward circuit is the total number of gates. Note that if any layer is
infinite, the whole sum will be zero. -/
noncomputable def size : ℕ :=
  Nat.card (@Sigma (Fin F.depth) (fun d ↦ F.nodes d.succ))

/-- We call a circuit finite if the number of nodes is finite. -/
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

/-
The set of inputs that a node at a given layer depends on. Defined by induction on the layer depth.
-/
def inputDeps (d : Fin (F.depth + 1)) : F.nodes d → Set inp :=
  @Fin.induction _ (fun d ↦ F.nodes d → Set inp)
    (fun n ↦ {cast F.nodes_zero n})
    (fun i ih n ↦ ⋃ j, ih ((F.gates i n).inputs j))
    d

/-
The set of input dependencies for a node at layer 0 is just the singleton set containing the corresponding input index.
-/
@[simp]
theorem inputDeps_zero (node : F.nodes 0) : F.inputDeps 0 node = { cast F.nodes_zero node } :=
  rfl

/-
The set of input dependencies for a node at layer `d+1` is the union of the input dependencies
of the nodes it depends on at layer `d`.
-/
theorem inputDeps_succ {d : Fin F.depth} (node : F.nodes d.succ) :
    F.inputDeps d.succ node = ⋃ i, F.inputDeps d.castSucc ((F.gates d node).inputs i) := by
  rfl

/-
If two inputs agree on the input dependencies of a node, then the node evaluates to the same value on both inputs.
-/
theorem evalNode_eq_of_eq_on_inputDeps {d : Fin (F.depth + 1)} {node : F.nodes d} {x y : inp → α}
    (h : ∀ i ∈ F.inputDeps d node, x i = y i) : F.evalNode node x = F.evalNode node y := by
  induction d using Fin.inductionOn
  · simpa using h
  rename_i a
  simp only [inputDeps_succ, Set.mem_iUnion, forall_exists_index] at h
  rw [FeedForward.evalNode]
  exact congrArg _ (funext fun x ↦ a fun y ↦ h y x)

/-
The essential domain of the function computed by a node is a subset of its input dependencies. This means that if an input is not in the set of input dependencies, changing it cannot affect the output of the node.
-/
theorem essDomain_subset_inputDeps {d : Fin (F.depth + 1)} (node : F.nodes d) :
    (F.evalNode node).EssDomain ⊆ F.inputDeps d node := by
  intro i hi
  contrapose! hi
  simp only [Function.EssDomain, Set.mem_setOf_eq, not_exists, not_and, not_not]
  intro x y _
  apply FeedForward.evalNode_eq_of_eq_on_inputDeps
  intro j _
  by_cases h : j = i <;> simp_all only [not_false_eq_true, ne_eq]

/-
The number of input dependencies of a node is bounded by `k^d`, where `k` is the maximum fan-in and `d` is the depth of the node. This is proved by induction on `d`.
-/
theorem inputDeps_card_le {d : Fin (F.depth + 1)} (node : F.nodes d) (k : ℕ)
    (h_fanin : ∀ d n, Finite (F.gates d n).op.ι ∧ Nat.card (F.gates d n).op.ι ≤ k) :
    (F.inputDeps d node).ncard ≤ k ^ (d : ℕ) := by
  induction d using Fin.inductionOn
  · simp
  rename_i i a
  simp only [Fin.coe_castSucc, Fin.val_succ] at a ⊢
  rcases h_fanin i node with ⟨ h₁, h₂ ⟩;
  have h_card_union : (Set.ncard (⋃ j : (F.gates i node).op.ι, F.inputDeps i.castSucc ((F.gates i node).inputs j))) ≤ (Nat.card (F.gates i node).op.ι) * k ^ (i : ℕ) := by
    have h_card_union : ∀ (s : Finset (F.gates i node).op.ι), (Set.ncard (⋃ j ∈ s, F.inputDeps i.castSucc ((F.gates i node).inputs j))) ≤ s.card * k ^ (i : ℕ) := by
      intro s
      induction s using Finset.induction
      · aesop
      · simp_all only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, not_false_eq_true, Finset.card_insert_of_notMem]
        rename_i a_1 a_2 s_1 a_3
        exact le_trans ( Set.ncard_union_le _ _ ) ( by linarith [ a ( ( F.gates i node ).inputs a_1 ) ] );
      · simp_all only
        exact Classical.decEq _;
    convert h_card_union ( Set.Finite.toFinset ( Set.finite_univ ) ) using 1 ; aesop;
    rw [ ← Nat.card_eq_finsetCard ] ; aesop;
  simpa only [ pow_succ' ] using h_card_union.trans ( Nat.mul_le_mul_right _ h₂ )

end FeedForward

open FeedForward

/-- A `CircuitFamily` is a collection of `FeedForward` circuits parameterized by an input size `n`.
The `n`th circuit must have input type `Fin n`, and a `Fin 1` output. -/
def CircuitFamily (α : Type u) :=
  (n : ℕ) → FeedForward α (Fin n) (Fin 1)

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
