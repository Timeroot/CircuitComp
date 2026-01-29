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

variable {α : Type u} {inp out a b c a₂ b₂ t₁ t₂ : Type v} (F : FeedForward α inp out)

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

theorem eval₁_eq_eval [Unique out] (xs : inp → α) (o : out):
    F.eval₁ xs = F.eval xs o := by
  rw [eval₁, Unique.default_eq]

/-- The cardinal width of a feedforward circuit is the largest number of nodes in any layer. -/
noncomputable def width_card : Cardinal :=
  ⨆ d, Cardinal.mk (F.nodes d)

/-- The size of a feedforward circuit is the total number of gates. Note that if any layer is
infinite, the whole sum will be zero. The inputs are nodes in the circuit but are not counted
towards the size. -/
noncomputable def size : ℕ :=
  Nat.card (@Sigma (Fin F.depth) (fun d ↦ F.nodes d.succ))

/-- We call a circuit finite if the number of nodes is finite. -/
protected abbrev Finite := ∀ i, Finite (F.nodes i)

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

/-- Relabel the output type of a `FeedForward` given an `Equiv`. -/
def relabelOut (hF : F.depth ≠ 0) (e : out ≃ a) : FeedForward α inp a :=
  haveI : NeZero F.depth := ⟨hF⟩
  { depth := F.depth
    nodes k := if k = ⊤ then a else F.nodes k
    gates k n := if hk : k = ⊤ then
        have g := F.gates k (by simp [Fin.top_eq_last, hk] at n ⊢; exact e.symm n)
        ⟨g.op, fun i ↦ by simpa [Fin.top_eq_last, hk] using g.inputs i⟩
      else cast (by simp [Fin.top_eq_last, (Fin.castSucc_lt_last k).ne])
        (F.gates k (cast (by simp [Fin.ext_iff] at hk ⊢; grind) n))
    nodes_zero := by simp [hF]
    nodes_last := by simp [Fin.top_eq_last]
  }

@[simp]
theorem relabelOut_depth (hf : F.depth ≠ 0) (e : out ≃ inp) :
    (F.relabelOut hf e).depth = F.depth := by
  rfl

def perm (e : t₁ ≃ t₂) : FeedForward α t₁ t₂ where
  depth := 1
  nodes k := if k = 0 then t₁ else t₂
  gates k n := ⟨GateOp.id α, fun i ↦ cast (by simp; omega) (e.symm (cast (by simp) n))⟩
  nodes_zero := by simp
  nodes_last := by simp

@[simp]
theorem perm_depth  (e : t₁ ≃ t₂) : (perm (α := α) e).depth = 1 := by
  rfl

@[simp]
theorem perm_size (e : t₁ ≃ t₂) : (perm (α := α) e).size = Nat.card t₂ := by
  rcases finite_or_infinite t₂ <;> simp [size, perm, Nat.card_sigma]

@[simp]
theorem perm_eval (e : t₁ ≃ t₂) : (perm (α := α) e).eval = (· ∘ e.symm) := by
  rfl

/-- Compose two `FeedForward`s by stacking one on top of the other. -/
def comp {a b c : Type v} (g : FeedForward α b c) (f : FeedForward α a b) : FeedForward α a c where
  depth := f.depth + g.depth
  nodes k := if h : k.val ≤ f.depth then f.nodes ⟨k, Nat.lt_add_one_of_le h⟩ else g.nodes ⟨k - f.depth, let _ := h; by omega⟩
  gates k n := if h : k.val < f.depth
    then cast
      (congrArg _ (dif_pos (Nat.le_of_succ_le h)).symm)
      (f.gates ⟨k.val, h⟩ (cast (dif_pos h) n))
    else cast
      (let _ := h; by
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
      (g.gates ⟨k.val - f.depth, let _ := h; by omega⟩
        (cast (let _ := h; by rw [dif_neg (by simp; omega)]; congr; simp; omega) n))
  nodes_zero := by simp
  nodes_last := by
    split_ifs with h
    · replace h : g.depth = 0 := by simpa using h
      refine Eq.trans ?_ (g.inp_eq_out_of_depth_zero h)
      simpa [-FeedForward.nodes_last, h] using f.nodes_last
    · simpa [-FeedForward.nodes_last] using g.nodes_last

@[simp]
theorem comp_depth (g : FeedForward α b c) (f : FeedForward α a b) :
    (g.comp f).depth = f.depth + g.depth := by
  rfl

/-
Helper lemma: The nodes of the composed circuit at depth `F.depth + j` correspond to the nodes of `G` at depth `j`.
-/
theorem comp_nodes_eq (F : FeedForward α a b) (G : FeedForward α b c) (j : Fin (G.depth + 1)) :
    (G.comp F).nodes ⟨F.depth + j.val, Nat.add_lt_add_left j.isLt F.depth⟩ = G.nodes j := by
  simp [FeedForward.comp]
  rintro rfl
  exact F.nodes_last.trans G.nodes_zero.symm

instance {t1} [i1 : F.Finite] (F2 : FeedForward α t1 inp) [i2 : F2.Finite] :
    (F.comp F2).Finite := by
  intro d
  change Fin (F2.depth + F.depth + 1) at d
  by_cases hd : d.val < F2.depth + 1
  · convert i2 (⟨d.val, by omega⟩)
    exact dif_pos (by omega)
  · convert i1 (⟨d - F2.depth, by omega⟩)
    rw [← comp_nodes_eq F2 F ⟨d - F2.depth, by omega⟩]
    congr!
    dsimp only
    omega

@[simp]
theorem comp_size (g : FeedForward α b c) (f : FeedForward α a b) [f.Finite] [g.Finite] :
    (g.comp f).size = f.size + g.size := by
  have h_comp_finite : (g.comp f).Finite := by
    intro
    dsimp [comp]
    grind
  dsimp [size]
  have h_split_sum : Nat.card (Σ d : Fin (f.depth + g.depth), (g.comp f).nodes d.succ) =
      Nat.card (Σ d : Fin f.depth, (g.comp f).nodes (d.castAdd g.depth).succ) +
      Nat.card (Σ d : Fin g.depth, (g.comp f).nodes (d.natAdd f.depth).succ) := by
    simp [Nat.card_sigma, Fin.sum_univ_add]
  convert h_split_sum using 2
  · simp [comp, Nat.succ_le_iff, Fin.succ]
  · simp [comp, add_assoc, Fin.succ]

/--
The evaluation of a node in the first part of a composed circuit `G.comp F` is
the same as its evaluation in `F`.
-/
theorem evalNode_comp_left {α : Type u} {a b c : Type v}
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
      · convert a_1 _ _ _
        grind
        exact Nat.lt_of_succ_lt pf;
        exact rfl;
    · grind

@[simp]
theorem evalNode_zero (F : FeedForward α inp out)
    (node : F.nodes 0) (xs : inp → α) :
    F.evalNode (d := 0) node xs = xs (F.nodes_zero ▸ node) := by
  simp [FeedForward.evalNode]

theorem evalNode_succ (F : FeedForward α inp out)
    (i : Fin F.depth) (node : F.nodes i.succ) (xs : inp → α) :
    F.evalNode node xs = (F.gates i node).eval (fun n ↦ F.evalNode n xs) := by
  rfl

/--
The evaluation of a node in the second part of a composed circuit `G.comp F` is
the same as its evaluation in `G` given the output of `F`.
-/
theorem evalNode_comp_right
    (F : FeedForward α a b) (G : FeedForward α b c)
    (j : Fin (G.depth + 1)) (node : G.nodes j) (x : a → α) :
    let k : Fin (F.depth + G.depth + 1) := ⟨F.depth + j.val, by omega⟩
    (G.comp F).evalNode (d := k) (cast (by simp [FeedForward.comp, k]; cases F; aesop) node) x = G.evalNode node (F.eval x) := by
  generalize_proofs pf1 pf2 pf3
  induction j using Fin.inductionOn
  · simp_all
    convert FeedForward.evalNode_comp_left F G ⟨ F.depth, Nat.lt_succ_self _ ⟩ _ x using 1;
    grind;
  · rename_i j ih
    rcases j with ⟨j, hj⟩
    dsimp [Fin.succ] at pf1 pf2 pf3 ih ⊢
    simp only [evalNode_succ, Fin.castSucc_mk]
    simp +zetaDelta at *;
    have h_eval_comp_succ : (G.comp F).evalNode (d := ⟨F.depth + (j + 1), pf2⟩) (cast pf3 node) x = ((G.comp F).gates ⟨F.depth + j, by
      rw [ FeedForward.depth ] at * ; linarith⟩ (cast pf3 node)).eval (fun n => (G.comp F).evalNode (d := ⟨F.depth + j, by
      linarith [ FeedForward.comp_depth G F ]⟩) n x) := by
      exact rfl
    generalize_proofs at *;
    have h_eval_comp_gates : (G.comp F).gates ⟨F.depth + j, by
      (expose_names; exact pf_3)⟩ (cast pf3 node) = cast (by
    all_goals generalize_proofs at *;
    have h_eval_comp_gates : (G.comp F).nodes ⟨F.depth + j, by
      linarith [ Nat.sub_add_cancel ( show F.depth ≤ F.depth + G.depth from Nat.le_add_right _ _ ) ]⟩ = G.nodes ⟨j, by
      linarith⟩ := by
      exact FeedForward.comp_nodes_eq F G ⟨j, by linarith⟩
    generalize_proofs at *;
    exact h_eval_comp_gates ▸ rfl) (G.gates ⟨j, hj⟩ node) := by
      all_goals generalize_proofs at *;
      simp +decide [ FeedForward.comp, * ];
      grind
    generalize_proofs at *;
    convert h_eval_comp_succ using 2;
    rw [ h_eval_comp_gates, FeedForward.Gate.eval, FeedForward.Gate.eval ];
    congr! 2
    generalize_proofs at *;
    · simp +zetaDelta at *;
      convert rfl;
      generalize_proofs at *;
      -- Since the cast is just a typecast and doesn't change the underlying data, the op should be the same. Therefore, the equality holds by definition of cast.
      apply Eq.symm
      have h_cast_eq : (G.comp F).nodes ⟨F.depth + j, by
        linarith⟩ = G.nodes ⟨j, by
        -- Since $j < G.depth$, we have $j < G.depth + 1$ by the properties of natural numbers.
        apply Nat.lt_succ_of_lt hj⟩ := by
        convert FeedForward.comp_nodes_eq F G ⟨ j, by linarith ⟩ using 1
      generalize_proofs at *
      grind
    · congr! 1;
    · convert ih _ _ _ _ |> Eq.symm using 1
      all_goals generalize_proofs at *;
      · simp +zetaDelta at *;
        grind;
      · linarith;
      · linarith;
      · convert FeedForward.comp_nodes_eq F G ⟨ j, by linarith ⟩ |> Eq.symm using 1

@[simp]
theorem eval_comp (F : FeedForward α a b) (G : FeedForward α b c) : (G.comp F).eval = G.eval ∘ F.eval := by
  funext x
  funext n
  simp [FeedForward.eval]
  convert FeedForward.evalNode_comp_right F G ( Fin.last G.depth ) _ _;
  grind

@[simp]
theorem eval₁_comp (F : FeedForward α a b) (G : FeedForward α b c) [Unique c] : (G.comp F).eval₁ = G.eval₁ ∘ F.eval := by
  ext1
  simp [eval₁]

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

theorem evalNode_sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂)
    (hf : f.depth = d) (hg : g.depth = d)
    (k : Fin (d + 1)) (node : (f.sum g hf hg).nodes k) (x : a ⊕ a₂ → α) :
    (f.sum g hf hg).evalNode node x = node.elim (f.evalNode · (x ∘ Sum.inl)) (g.evalNode · (x ∘ Sum.inr)) := by
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

theorem eval_sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂)
    (hf : f.depth = d) (hg : g.depth = d) :
    ∀ (x : a ⊕ a₂ → α), (f.sum g hf hg).eval x = Sum.elim (f.eval (x ∘ .inl)) (g.eval (x ∘ .inr)) := by
  intro x
  ext
  unfold FeedForward.eval
  convert FeedForward.evalNode_sum f g hf hg (Fin.last d) _ x using 2
  simp only [Fin.cast, Fin.val_last]
  congr
  · exact f.nodes_last.symm.trans (by congr; aesop)
  · exact g.nodes_last.symm.trans (by congr; aesop)
  · congr! 3
    · exact hf ▸ f.nodes_last.symm
    · grind
  · congr! 3
    · exact hg ▸ g.nodes_last.symm
    · grind
  · grind

instance {t1 t2} [Finite t1] (e : t1 ≃ t2) : (perm (α := α) e).Finite := by
  intros i
  cases i using Fin.inductionOn <;> simp [FeedForward.perm];
  · grind
  · exact (Equiv.finite_iff e).mp ‹_›

/-- A `FeedForward` is said to `onlyUsesGates` from a set of `GateOp`s if every gate is one of those. -/
def onlyUsesGates (S : Set (GateOp α)) : Prop :=
  ∀ d n, (F.gates d n).op ∈ S

variable {F} {S T : Set (GateOp α)}

theorem onlyUsesGates_mono (hS : S ⊆ T) (hF : F.onlyUsesGates S) :
    F.onlyUsesGates T := by
  intro d n
  specialize hF d n
  exact hS hF

theorem onlyUsesGates_comp {t2 : Type v} {F2 : FeedForward α out t2}
    (hF : F.onlyUsesGates S) (hF2 : F2.onlyUsesGates S) : (F2.comp F).onlyUsesGates S := by
  intro d n
  dsimp [comp] at n ⊢
  by_cases h : d < F.depth;
  · convert hF ⟨d, h⟩ (cast (by symm; simp; intro; omega) n)
    simp [h]
    grind
  · have h_cast : (d.val - F.depth) < F2.depth := by grind [comp_depth]
    convert hF2 ⟨d - F.depth, h_cast⟩
      (cast (by split_ifs <;> simp_all [ Nat.succ_sub ]; omega) n) using 1
    simp [h]
    congr 1
    · split_ifs
      · simp [show d = F.depth by omega]
        exact F.nodes_last
      · rfl
    · exact cast_heq _ _

theorem onlyUsesGates_perm {t₁ t₂ : Type v} {e : t₁ ≃ t₂} :
    (perm e).onlyUsesGates {GateOp.id α} := by
  simp [onlyUsesGates, perm]

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
def CircuitFamily (α : Type u) (out : ℕ → Type) :=
  (n : ℕ) → FeedForward α (Fin n) (out n)

/-- Abbreviation for `CircuitFamily` where the output is a single value. Note that for universe
reasons about the types inside the circuit, this means that the output type `out` must be in
`Type` and not a higher universe. In principle this is not an issue, since it always has
cardinality 1.

Letting `out` vary rather than be fixed (to a `Unit` or `Fin 1`) makes it easier
to work with more uniform constructions: for instance, a circuit could have nodes of type
`Fin i → Fin 2` at depth `i` from the end, which would end in the `Unique` type `Fin 0 → Fin 2`
for the final layer. If we requirea `Unit` out, then we would need to do a relabelling at the
end, complicating the types significantly. -/
abbrev CircuitFamily₁ (α : Type u) (out) [Unique out] :=
  CircuitFamily α (fun _ ↦ out)

namespace CircuitFamily

variable {α : Type u} {out : ℕ → Type} (CF : CircuitFamily α out)

/-- A `CircuitFamily` `computes` a function family if that is given by its `eval`.-/
def computes (F : FuncFamily α out) : Prop :=
  ∀ n, (CF n).eval = F n

/-- Predicate expressing that the depth grows as O(f n). -/
def hasDepth (f : GrowthRate) : Prop :=
  (fun n ↦ (CF n).depth) ∈ f

/-- Predicate expressing that all circuits in the family are finite. -/
protected abbrev Finite := ∀ n, (CF n).Finite

instance [inst : CF.Finite] {n} : (CF n).Finite :=
  inst n

/-- Predicate expressing that the size grows as O(f n). -/
def hasSize (f : GrowthRate) [CF.Finite]: Prop :=
  (fun n ↦ (CF n).size) ∈ f

/-- A `CircuitFamily` is said to `onlyUsesGates` from a set of `GateOp`s if every gate is one of those. -/
def onlyUsesGates (S : Set (GateOp α)) : Prop :=
  ∀ n, (CF n).onlyUsesGates S

@[simp]
lemma FeedForward.size_relabelOut {α inp out a} (F : FeedForward α inp out) (hF : F.depth ≠ 0) (e : out ≃ a) :
    (F.relabelOut hF e).size = F.size := by
  unfold FeedForward.size at *;
  simp +decide [ Nat.card ];
  -- Since the relabeling only affects the last layer's nodes, and we're summing over all layers, this shouldn't change the total sum. Therefore, the two sums should be equal.
  have h_sum_eq : ∀ i : Fin F.depth, Cardinal.mk (if i.succ = Fin.last F.depth then a else F.nodes i.succ) = Cardinal.mk (F.nodes i.succ) := by
    intro i; split_ifs <;> simp_all +decide [ Fin.ext_iff ] ;
    rw [ show F.nodes i.succ = out from _ ];
    · exact Cardinal.mk_congr e.symm;
    · convert F.nodes_last;
      exact Fin.ext ( by simp +decide [ * ] );
  grind

instance {α inp out a} (F : FeedForward α inp out) (hF : F.depth ≠ 0) (e : out ≃ a) [Finite a] [F.Finite] :
    (F.relabelOut hF e).Finite := by
  intro i
  dsimp only [relabelOut]
  split_ifs
  · infer_instance
  · infer_instance

end CircuitFamily

namespace CircuitFamily₁

variable {α : Type u} {out : Type} [Unique out] (CF : CircuitFamily₁ α out)

/-- A `CircuitFamily₁` is said to `computes` a function family if that is given by its `eval₁`.-/
def computes₁ (F : FuncFamily₁ α) : Prop :=
  ∀ n, (CF n).eval₁ = F n

theorem computes_iff_computes₁ (F : FuncFamily₁ α) :
    CF.computes₁ F ↔ CircuitFamily.computes CF (F.toFuncFamily out):= by
  constructor <;> intro h n <;> funext
  · rw [FuncFamily₁.toFuncFamily, Equiv.coe_fn_mk, ← h, eval₁_eq_eval]
  · simp [CircuitFamily.computes, FuncFamily₁.toFuncFamily] at h
    rw [eval₁, h n]

abbrev hasDepth (f : GrowthRate) := CircuitFamily.hasDepth CF f

protected abbrev Finite := CircuitFamily.Finite CF

abbrev hasSize [CF.Finite] (f : GrowthRate) := CircuitFamily.hasSize CF f

abbrev onlyUsesGates (S : Set (GateOp α)) := CircuitFamily.onlyUsesGates CF S

variable {CF} {S T : Set (GateOp α)}

theorem onlyUsesGates_mono (hS : S ⊆ T) (hCF : onlyUsesGates CF S) :
  CF.onlyUsesGates T := by
  intro n
  exact FeedForward.onlyUsesGates_mono hS (hCF n)

end CircuitFamily₁

open CircuitFamily₁

/-- A `CircuitClass` is a set of function families defined by circuits on a given set of gates,
a bound on depth, and a bound on size. This definition lets `out` be any type we like. -/
def CircuitClass {α : Type*} (size : GrowthRate) (depth : GrowthRate) (gates : Set (GateOp α))
    : Set (FuncFamily₁ α) :=
  fun fs ↦ ∃ (out : Type) (_ : Unique out) (CF : CircuitFamily₁ α out) (_ : CF.Finite),
    CF.computes₁ fs
    ∧ CF.hasSize size
    ∧ CF.hasDepth depth
    ∧ CF.onlyUsesGates gates

section circuitClass

variable {α : Type*} (size : GrowthRate) (depth : GrowthRate) (gates : Set (GateOp α))
variable (fs : FuncFamily₁ α)

theorem CircuitClass.Monotone_size : Monotone (CircuitClass · depth gates) := by
  rintro s₁ s₂ hs fs ⟨o, u, CF, h_fin, h_comp, h_size, h_depth, h_gates⟩
  exact ⟨o, u, CF, h_fin, h_comp, hs h_size, h_depth, h_gates⟩

theorem CircuitClass.Monotone_depth : Monotone (CircuitClass size · gates) := by
  rintro d₁ d₂ hd fs ⟨o, u, CF, h_fin, h_comp, h_size, h_depth, h_gates⟩
  exact ⟨o, u, CF, h_fin, h_comp, h_size, hd h_depth, h_gates⟩

theorem CircuitClass.Monotone_gates : Monotone (CircuitClass (α := α) size depth ·) := by
  rintro g₁ g₂ hg fs ⟨o, u, CF, h_fin, h_comp, h_size, h_depth, h_gates⟩
  exact ⟨o, u, CF, h_fin, h_comp, h_size, h_depth, onlyUsesGates_mono hg h_gates⟩

theorem mem_circuitClass_iff_exists_out : fs ∈ CircuitClass size depth gates ↔
    ∃ (out : Type) (_ : Unique out),
      ∃ (CF : CircuitFamily₁ α out) (_ : CF.Finite),
        CF.computes₁ fs
        ∧ CF.hasSize size
        ∧ CF.hasDepth depth
        ∧ CF.onlyUsesGates gates := by
  rfl

--We want to say that the choice of output type doesn't matter, so long as it's unique.
--There's a stupid catch though: what if `depth` is zero at some n? Then the only
--circuits (for that n) we have are those where the input and output depth are the same,
--so it's actually not true that the choice of output type doesn't matter. With an appropriate
--nontrivialy condition, we can rule out this case: just add an extra gate at the end
--that changes the output type to the desired one. This extra gate has size and depth 1,
--so it suffices to assunme that depth and size are `LawfulGrowthRate`.

variable [LawfulGrowthRate size] [LawfulGrowthRate depth]

theorem mem_circuitClass_iff_forall_out (h_id : GateOp.id α ∈ gates) :
  fs ∈ CircuitClass size depth gates ↔
  ∀ (out : Type) [Unique out],
    ∃ (CF : CircuitFamily₁ α out) (_ : CF.Finite),
      CF.computes₁ fs
      ∧ CF.hasSize size
      ∧ CF.hasDepth depth
      ∧ CF.onlyUsesGates gates := by
  rw [mem_circuitClass_iff_exists_out]
  refine ⟨?_, fun h ↦ ⟨Unit, _, h Unit⟩⟩
  intro ⟨out, u, CF, h_fin, h_comp, h_size, h_depth, h_gates⟩ out₂ _
  use fun n ↦ (perm (Equiv.ofUnique out out₂)).comp (CF n)
  use inferInstance
  and_intros
  · intro n
    ext1
    simp [← h_comp n, eval₁, perm_eval]
  · simp [CircuitFamily.hasSize]
    exact GrowthRate.add h_size GrowthRate.one_mem
  · simp [CircuitFamily.hasDepth]
    exact GrowthRate.add h_depth GrowthRate.one_mem
  · intro n
    apply onlyUsesGates_comp (h_gates n)
    exact FeedForward.onlyUsesGates_mono (by simpa) onlyUsesGates_perm

variable {size depth gates fs} in
theorem mem_circuitClass_iff (h_id : GateOp.id α ∈ gates) (out : Type) [Unique out] :
  fs ∈ CircuitClass size depth gates ↔
    ∃ (CF : CircuitFamily₁ α out) (_ : CF.Finite),
        CF.computes₁ fs
        ∧ CF.hasSize size
        ∧ CF.hasDepth depth
        ∧ CF.onlyUsesGates gates := by
  constructor
  · rw [mem_circuitClass_iff_forall_out]
    · exact fun h ↦ h out
    · exact h_id
  · rw [mem_circuitClass_iff_exists_out]
    exact fun h ↦ ⟨out, _, h⟩

end circuitClass
