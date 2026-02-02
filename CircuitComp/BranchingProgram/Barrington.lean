
import CircuitComp.NC
import CircuitComp.BranchingProgram.Basic

import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!

# Barrington's Theorem on Short Branching Programs of Width 5

Barrington's theorem states that any function computable by a formula with
AND, OR, and NOT gates can be computed by a branching program of width 5 and depth at
most $4^d$ for a formula with depth $d$.

This includes, as an important consequence, that in polynomial size we can compute any
function in NC^1, since they have logarithmic depth (and thus polynomial size - and the
distinction between circuits and formulas is not important).

To prove this, an auxiliary type of computation is used: a "group program", which is a
program that computes a function in a group. This is a more specific type of computation
than a branching program.
-/
noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}

open LayeredBranchingProgram

/--
Define GroupProgram and its evaluation. The type `g` is typically a group (but in general
just needs some multiplicative structure). The types `perm0` and `perm1` are used depending on
the value of each variable, indexed by the types `α`.

This is also sometimes called a "Barrington program", or "Barrington branching program".
-/
structure GroupProgram (α : Type u) (G : Type v) where
  len : ℕ
  var : Fin len → α
  perm0 : Fin len → G
  perm1 : Fin len → G

namespace GroupProgram

variable {α : Type u} {G : Type v} (GP GP1 GP2 : GroupProgram α G)

/-- A group program evaluates to a group element based on the product. -/
def eval [Mul G] [One G] (x : α → Fin 2) : G :=
  (List.finRange GP.len).foldl (fun acc i ↦
    let p := if x (GP.var i) = 1 then GP.perm1 i else GP.perm0 i
    p * acc) (1 : G)

/-- A group program `computes` a binary function f if the `GroupProgam.eval` gives
a `σ ^ (f x)`. -/
def computes [Mul G] [One G] (f : (α → Fin 2) → Fin 2) (σ : G) : Prop :=
  ∀ x, GP.eval x = if f x = 1 then σ else 1

/--
The concatenation of two group programs, such that the evaluation of the
concatenated program is the product of the evaluations (note the order due to function
composition/multiplication convention).
-/
def append : GroupProgram α G where
  len := GP1.len + GP2.len
  var := Fin.append GP1.var GP2.var
  perm0 := Fin.append GP1.perm0 GP2.perm0
  perm1 := Fin.append GP1.perm1 GP2.perm1

theorem len_append : (append GP1 GP2).len = GP1.len + GP2.len :=
  rfl

theorem eval_append [Monoid G] (GP1 GP2 : GroupProgram α G) (x : α → Fin 2) :
    (GP1.append GP2).eval x = GP2.eval x * GP1.eval x := by
  unfold append eval;
  rw [ show List.finRange (GP1.len + GP2.len) = List.map (Fin.castAdd GP2.len) (List.finRange GP1.len) ++ List.map ( fun i => Fin.natAdd GP1.len i ) ( List.finRange GP2.len ) from ?_, List.foldl_append ];
  · simp [Fin.append, List.foldl_map]
    induction (List.finRange GP2.len) using List.reverseRecOn
    · simp
    · simp_all [mul_assoc]
  · apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      by_cases hi₃ : i < GP1.len
      · simp [hi₃]
      · simp_all
/--
The reverse of a group program, whose evaluation is the inverse of the original program's evaluation.
-/
def reverse [Inv G] : GroupProgram α G where
  len := GP.len
  var := GP.var ∘ Fin.rev
  perm0 := fun i ↦ (GP.perm0 (Fin.rev i))⁻¹
  perm1 := fun i ↦ (GP.perm1 (Fin.rev i))⁻¹

theorem eval_reverse [Group G] (x : α → Fin 2) :
    GP.reverse.eval x = (GP.eval x)⁻¹ := by
  unfold eval reverse
  -- By definition of `List.finRange`, we can rewrite the left-hand side to match the right-hand side.
  have h_finRange : List.finRange GP.len = List.map (fun i => Fin.rev i) (List.finRange GP.len).reverse := by
    refine' List.ext_get _ _ <;> simp [ Fin.rev ];
    exact fun i hi => by omega;
  conv_rhs => rw [ h_finRange ];
  induction' ( List.finRange GP.len ) using List.reverseRecOn with i _ ih <;> simp [ * ];
  split_ifs <;> simp_all +singlePass [ List.foldr_map];
  · induction i
    · simp
    simp only [Fin.isValue, List.foldr_cons]
    split_ifs <;> simp [*, ← mul_assoc]
  · induction i
    · simp
    simp only [Fin.isValue, List.foldr_cons]
    split_ifs <;> simp [*, ← mul_assoc]

/--
A group program for a single variable.
-/
def ofVar (i : α) [One G] (σ : G) : GroupProgram α G where
  len := 1
  var := fun _ ↦ i
  perm0 := fun _ ↦ 1
  perm1 := fun _ ↦ σ

theorem eval_ofVar [MulOneClass G] (i : α) (σ : G) (x : α → Fin 2) :
    (GroupProgram.ofVar i σ).eval x = if x i = 1 then σ else 1 := by
  simp [ofVar, eval, List.finRange_succ]

/--
A constant group program (reading a dummy variable) that evaluates to the constant permutation.
-/
def const (i : α) (σ : G) : GroupProgram α G where
  len := 1
  var := fun _ ↦ i
  perm0 := fun _ ↦ σ
  perm1 := fun _ ↦ σ

theorem eval_const [MulOneClass G] (i : α) (σ : G) (x : α → Fin 2) :
    (GroupProgram.const i σ).eval x = σ := by
  simp [eval, const, Fin.isValue, ite_self, List.finRange_succ]

/-
Define the commutator of two group programs, whose length is twice the sum of the lengths
of the original programs.
-/
def commutator [Inv G] : GroupProgram α G :=
  (GP1.append GP2).append (GP1.reverse.append GP2.reverse)

theorem len_commutator [Inv G] :
    (GP1.commutator GP2).len = 2 * GP1.len + 2 * GP2.len := by
  simp +arith [commutator, len_append, reverse]

/--
The evaluation of the commutator program is the commutator of the evaluations.
-/
theorem eval_commutator [Group G] (x : α → Fin 2) :
    (GP1.commutator GP2).eval x = (GP2.eval x)⁻¹ * (GP1.eval x)⁻¹ * GP2.eval x * GP1.eval x := by
  unfold commutator;
  rw [eval_append, eval_append, eval_append, eval_reverse, eval_reverse]
  group

/--
The conversion from a Group Program to a Layered Branching Program.
-/
def toBranchingProgram (σ : G) (γ : Type) [Zero γ] [DecidableEq γ] [SMul G γ] :
    LayeredBranchingProgram α (Fin 2) (Fin 2) where
  depth := GP.len
  nodes := fun i ↦ if i.val = 0 then Fin 1 else γ
  nodeVar := fun {k} _ ↦ GP.var k
  edges := fun {k} u b ↦
    if hk : k.val = 0 then
      let p := if b = 1 then GP.perm1 k else GP.perm0 k
      let dest : γ := p • 0
      dest
    else
      let u' : γ := cast (by simp [hk]) u
      let p := if b = 1 then GP.perm1 k else GP.perm0 k
      p • u'
  startUnique := {
    default := cast (by simp) (0 : Fin 1)
    uniq := fun x ↦ Fin.eq_zero _
  }
  retVals := fun u ↦
    if h : GP.len = 0 then
      0
    else
      let u' : γ := cast (by simp [h]) u
      if u' = σ • 0 then 1 else 0

/--
The width of the converted branching program is bounded by the cardinality of the target type.
When `G` is `Equiv.Perm (Fin 5)` and `γ` is `Fin 5`, this is at most 5.
-/
theorem width_toBranchingProgram (σ : G)
    (γ : Type) [Zero γ] [DecidableEq γ] [SMul G γ] [Fintype γ] :
    (GP.toBranchingProgram σ γ).width ≤ Fintype.card γ := by
  apply ciSup_le
  unfold toBranchingProgram
  intro x
  simp only [Fin.val_eq_zero_iff]
  split
  · subst x
    simp
    apply Fintype.card_pos
  · simp


/--
Any 5-cycle in $S_5$ can be written as a commutator of two 5-cycles.
-/
theorem _root_.exists_commutator_eq_cycle (σ : Equiv.Perm (Fin 5)) (hσ : σ.IsCycle ∧ σ.support.card = 5) :
    ∃ α β : Equiv.Perm (Fin 5),
      α.IsCycle ∧ α.support.card = 5 ∧
      β.IsCycle ∧ β.support.card = 5 ∧
      σ = α * β * α⁻¹ * β⁻¹ := by
  revert σ
  simp [Equiv.Perm.IsCycle]
  native_decide +revert

/-
Prove that `ofVar` computes the projection function.
-/
theorem computes_ofVar {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) :
    (GroupProgram.ofVar i σ).computes (fun x ↦ x i) σ := by
  unfold computes; aesop

/-
Prove that the commutator of two group programs computes the AND of their functions, given that the resulting commutator permutation is non-identity.
-/
theorem computes_and [Group G] (f g : (α → Fin 2) → Fin 2) (a b : G)
      (h1 : GP1.computes f a) (h2 : GP2.computes g b) :
    (GP1.commutator GP2).computes (fun x ↦ f x * g x) (b⁻¹ * a⁻¹ * b * a) := by
  unfold computes at *
  refine fun x ↦ ?_
  simp [ *, GroupProgram.eval_commutator ]
  split_ifs <;> simp_all [ mul_assoc ]
  grind

/-
The negation of a group program appends a constant program that applies σ.
Requires a dummy variable index i to construct the constant program.
-/
def negate [Group G] (i : α) (σ : G) : GroupProgram α G :=
  GP.append (GroupProgram.const i σ)

/-
The length of the negated program is the length of the original program plus 1.
-/
theorem len_negate [Group G] (i : α) (σ : G) :
    (GP.negate i σ).len = GP.len + 1 := by
  unfold negate
  rw [len_append]
  rfl

/-
Prove that the negation of a group program computes the negation of the function.
-/
theorem computes_negate [Group G] (i : α) (f : (α → Fin 2) → Fin 2) (σ : G)
    (h : GP.computes f σ⁻¹) :
    (GP.negate i σ).computes (fun x ↦ 1 - f x) σ := by
  simp_all [ computes ];
  intro x; have := h x; simp_all [ eval_append, negate ] ;
  cases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ <;> simp_all [ eval_const ]

end GroupProgram

/-
Classify the gates in NC_GateOps into AND, NOT, ID, and Const 1.
-/
open FeedForward

def FeedForward.GateOp.isAND (op : GateOp (Fin 2)) : Prop :=
  ∃ e : op.ι ≃ Fin 2, ∀ x, op.func x = x (e.symm 0) * x (e.symm 1)

def FeedForward.GateOp.isNOT (op : GateOp (Fin 2)) : Prop :=
  ∃ e : op.ι ≃ Fin 1, ∀ x, op.func x = 1 - x (e.symm 0)

def FeedForward.GateOp.isID (op : GateOp (Fin 2)) : Prop :=
  ∃ e : op.ι ≃ Fin 1, ∀ x, op.func x = x (e.symm 0)

def FeedForward.GateOp.isConst (op : GateOp (Fin 2)) (c : Fin 2) : Prop :=
  IsEmpty op.ι ∧ ∀ x, op.func x = c

theorem NC_gates_cases (op : GateOp (Fin 2)) (h : op ∈ NC_GateOps) :
    op.isAND ∨ op.isNOT ∨ op.isID ∨ op.isConst 1 := by
  revert h
  simp [NC_GateOps]
  rintro (rfl | rfl | rfl | rfl) <;> simp +decide [GateOp.isAND, GateOp.isNOT, GateOp.isID, GateOp.isConst];
  exact Fin.isEmpty'

/--
The recursive step for constructing a group program from a circuit layer.
-/
noncomputable def GP_of_FeedForward_layer {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) : GroupProgram (Fin n) (Equiv.Perm (Fin 5)) :=
  open Classical in
  let g := gates u
  if h_and : g.op.isAND then
    let e := Classical.choose h_and
    let v0 := g.inputs (e.symm 0)
    let v1 := g.inputs (e.symm 1)
    if h_cycle : σ.IsCycle ∧ σ.support.card = 5 then
      let x := Classical.choose (exists_commutator_eq_cycle σ h_cycle)
      let y := Classical.choose (Classical.choose_spec (exists_commutator_eq_cycle σ h_cycle))
      (prev_GPs v0 y⁻¹).commutator (prev_GPs v1 x⁻¹)
    else
      GroupProgram.const ⟨0, hn⟩ 1
  else if h_not : g.op.isNOT then
    let e := Classical.choose h_not
    let v := g.inputs (e.symm 0)
    (prev_GPs v σ⁻¹).negate ⟨0, hn⟩ σ
  else if h_id : g.op.isID then
    let e := Classical.choose h_id
    let v := g.inputs (e.symm 0)
    prev_GPs v σ
  else
    GroupProgram.const ⟨0, hn⟩ σ

/--
The full group program construction by induction on the circuit depth.
-/
noncomputable def GP_of_FeedForward {n : ℕ} (hn : n > 0)
    {out : Type} [Unique out] (F : FeedForward (Fin 2) (Fin n) out)
    (d : Fin (F.depth + 1)) :
    F.nodes d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)) :=
  @Fin.induction _ (fun d => F.nodes d →
      (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (fun i σ =>
      GroupProgram.ofVar (cast F.nodes_zero i) σ)
    (fun d prev_GPs => GP_of_FeedForward_layer hn (F.gates d) prev_GPs)
    d

/--
The length of the constructed group program layer is at most 4 times the maximum length of the previous layer programs.
-/
theorem GP_of_FeedForward_layer_len {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    {prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5))}
    {L : ℕ} (hL : 1 ≤ L)
    (h_prev : ∀ v σ, (prev_GPs v σ).len ≤ L)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).len ≤ 4 * L := by
  unfold GP_of_FeedForward_layer;
  dsimp only [Fin.isValue]
  split_ifs <;> norm_num [ GroupProgram.len_commutator, GroupProgram.len_negate ];
  · grind;
  · exact Nat.one_le_iff_ne_zero.mpr ( by positivity );
  · linarith [ h_prev ( ( gates u ).inputs ( ( Classical.choose ‹ ( gates u |> Gate.op ) |> GateOp.isNOT › ).symm 0 ) ) σ⁻¹ ];
  · grind;
  · exact Nat.one_le_iff_ne_zero.mpr ( by positivity )

/-
The length of the constructed group program is at most $4^d$.
-/
theorem GP_of_FeedForward_len {out : Type} [Unique out] {n : ℕ} (hn : n > 0)
    (F : FeedForward (Fin 2) (Fin n) out)
    (d : Fin (F.depth + 1)) (u : F.nodes d) (σ : Equiv.Perm (Fin 5)) :
    (GP_of_FeedForward hn F d u σ).len ≤ 4 ^ (d : ℕ) := by
  induction' d using Fin.induction with d ih generalizing σ;
  · exact Nat.le_of_ble_eq_true rfl;
  · simp only [Fin.val_succ, pow_succ']
    exact GP_of_FeedForward_layer_len hn (F.gates d) (Nat.one_le_pow' d 3) ih u σ

/-
A gate cannot be both a NOT gate and an AND gate.
-/
lemma not_isAND_of_isNOT {op : FeedForward.GateOp (Fin 2)} (h : op.isNOT) : ¬op.isAND := by
  obtain ⟨e_not, he_not⟩ := h
  rintro ⟨e_and, he_and⟩
  have := Equiv.cardinal_eq e_not
  have := Equiv.cardinal_eq e_and
  simp_all

/-
If the gate is a NOT gate, the constructed group program computes the negation of the input.
-/
theorem GP_of_FeedForward_layer_computes_NOT {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_GPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_not : (gates u).op.isNOT) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).computes
      (fun x ↦ (gates u).eval (input_vals · x)) σ := by
  unfold GP_of_FeedForward_layer
  field_simp
  split_ifs with h
  · exact False.elim <| not_isAND_of_isNOT h_not h
  · convert GroupProgram.computes_negate _ _ (input_vals ((gates u).inputs (h_not.choose.symm 0))) _ _ using 1
    · funext x
      exact h_not.choose_spec _
    · exact h_prev _ _ ⟨by simpa using hσ.1.inv, by simpa using hσ.2⟩

/-
If the gate is an ID gate, the constructed group program computes the identity of the input.
-/
theorem GP_of_FeedForward_layer_computes_ID {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_GPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_id : (gates u).op.isID) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
    have h_not_and : ¬(gates u).op.isAND := by
      obtain ⟨ e, he ⟩ := h_id;
      rintro ⟨ e', he' ⟩;
      have := e.cardinal_eq; have := e'.cardinal_eq; aesop;
    unfold GP_of_FeedForward_layer;
    have h_not_not : ¬(gates u).op.isNOT := by
      intro h_not;
      obtain ⟨e, he⟩ := h_id
      obtain ⟨e', he'⟩ := h_not
      have h_eq : e.symm 0 = e'.symm 0 := by
        have := e.symm.surjective ( e'.symm 0 ) ; have := e'.symm.surjective ( e.symm 0 ) ; aesop;
      have := he fun _ => 0; have := he' fun _ => 0; simp_all ;
    simp [h_not_and, h_not_not, h_id];
    convert h_prev _ _ hσ using 2;
    exact h_id.choose_spec _

/-
If the gate is a Const 1 gate, the constructed group program computes the constant 1 function.
-/
theorem GP_of_FeedForward_layer_computes_Const {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_const : (gates u).op.isConst 1) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
  apply Classical.byContradiction
  intro h_not_const;
  -- Since the gate is not a constant 1, it must be either an AND or a NOT gate.
  by_cases h_and : (gates u).op.isAND ∨ (gates u).op.isNOT ∨ (gates u).op.isID;
  · obtain h | h | h := h_and <;> simp_all [ FeedForward.GateOp.isAND, FeedForward.GateOp.isNOT, FeedForward.GateOp.isID, FeedForward.GateOp.isConst ];
    · exact h_const.1.elim ( Classical.choose h |> Equiv.symm |> Equiv.toEmbedding |> fun e => e 0 );
    · exact h_const.1.elim ( h.choose.symm 0 );
    · obtain ⟨ e, he ⟩ := h;
      exact h_const.1.elim ( e.symm 0 );
  · unfold GP_of_FeedForward_layer at h_not_const; simp_all ;
    unfold GroupProgram.computes at h_not_const; simp_all ;
    obtain ⟨ x, hx ⟩ := h_not_const
    simp_all [ GroupProgram.eval_const ] ;
    unfold Gate.eval at hx; simp_all [ GateOp.isConst ] ;

/-
If `σ` is the commutator of `x` and `y`, and `GP1` computes `f` with `y⁻¹` and `GP2` computes `g` with `x⁻¹`, then the commutator of `GP1` and `GP2` computes `f * g` with `σ`.
-/
lemma commutator_computes_AND_of_cycle_decomp {n : ℕ} (GP1 GP2 : GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (f g : (Fin n → Fin 2) → Fin 2) (σ x y : Equiv.Perm (Fin 5))
    (h_decomp : σ = x * y * x⁻¹ * y⁻¹)
    (h1 : GP1.computes f y⁻¹)
    (h2 : GP2.computes g x⁻¹) :
    (GP1.commutator GP2).computes (fun z ↦ f z * g z) σ := by
  convert GroupProgram.computes_and GP1 GP2 f g (y⁻¹) (x⁻¹) h1 h2

/-
The inverse of a 5-cycle is a 5-cycle.
-/
lemma inv_is_five_cycle (σ : Equiv.Perm (Fin 5)) (h : σ.IsCycle ∧ σ.support.card = 5) :
    σ⁻¹.IsCycle ∧ σ⁻¹.support.card = 5 := by
  simp [h]

/-
If a gate is an AND gate, its evaluation is the product of the values of its two inputs.
-/
lemma Gate_eval_of_isAND {domain : Type*} {g : FeedForward.Gate (Fin 2) domain}
    (h_and : g.op.isAND) (x : domain → Fin 2) :
    g.eval x = x (g.inputs ((Classical.choose h_and).symm 0)) * x (g.inputs ((Classical.choose h_and).symm 1)) :=
  (Classical.choose_spec h_and) fun x_1 ↦ x (g.inputs x_1)

/-
If the gate is an AND gate, the constructed group program computes the AND of the inputs.
-/
theorem GP_of_FeedForward_layer_computes_AND {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_GPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_and : (gates u).op.isAND) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
  have h_apply_def : ∀ {w : Equiv.Perm (Fin 5)}, w.IsCycle ∧ w.support.card = 5 → (GP_of_FeedForward_layer hn gates prev_GPs u w).computes (fun x => (gates u).eval (fun v => input_vals v x)) w := by
    intros w hw
    unfold GP_of_FeedForward_layer;
    simp_all +decide only;
    split_ifs ; simp_all +decide only [Gate_eval_of_isAND];
    · apply_rules [ commutator_computes_AND_of_cycle_decomp ];
      · have := Classical.choose_spec ( exists_commutator_eq_cycle w hw );
        exact this.choose_spec.2.2.2.2;
      · apply_rules [ inv_is_five_cycle ];
        exact Classical.choose_spec ( exists_commutator_eq_cycle w hw ) |> Classical.choose_spec |> And.right |> And.right |> And.left |> fun h => ⟨ h, by
          exact Classical.choose_spec ( exists_commutator_eq_cycle w hw ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.left ⟩;
      · apply_rules [ inv_is_five_cycle ];
        exact Classical.choose_spec ( exists_commutator_eq_cycle w hw ) |> Classical.choose_spec |> fun h => ⟨ h.1, h.2.1 ⟩;
    · contradiction;
  exact h_apply_def hσ

/-
Simplification lemma for `GP_of_FeedForward_layer` in the AND case.
-/
lemma GP_of_FeedForward_layer_eq_commutator {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (h_and : (gates u).op.isAND)
    (h_cycle : σ.IsCycle ∧ σ.support.card = 5) :
    GP_of_FeedForward_layer hn gates prev_GPs u σ =
      let e := Classical.choose h_and
      let x := Classical.choose (exists_commutator_eq_cycle σ h_cycle)
      let y := Classical.choose (Classical.choose_spec (exists_commutator_eq_cycle σ h_cycle))
    (prev_GPs ((gates u).inputs (e.symm 0)) y⁻¹).commutator (prev_GPs ((gates u).inputs (e.symm 1)) x⁻¹) := by
  simp_all [GP_of_FeedForward_layer]

/-
The group program constructed for a layer computes the correct value, assuming the previous layer's programs are correct.
-/
theorem GP_of_FeedForward_layer_computes {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_GPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_gates : (gates u).op ∈ NC_GateOps) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
  rcases (NC_gates_cases (gates u).op h_gates) with h | h | h | h
  · exact GP_of_FeedForward_layer_computes_AND hn gates prev_GPs input_vals h_prev u σ hσ h
  · exact GP_of_FeedForward_layer_computes_NOT hn gates prev_GPs input_vals h_prev u σ hσ h
  · exact GP_of_FeedForward_layer_computes_ID hn gates prev_GPs input_vals h_prev u σ hσ h
  · exact GP_of_FeedForward_layer_computes_Const hn gates prev_GPs input_vals u σ hσ h

/-
The group program constructed from a FeedForward circuit computes the same function as the circuit node.
-/
theorem GP_of_FeedForward_computes {n : ℕ} (hn : n > 0)
    {out : Type} [Unique out] {F : FeedForward (Fin 2) (Fin n) out}
    (h_gates : F.onlyUsesGates NC_GateOps)
    {d : Fin (F.depth + 1)} (u : F.nodes d) {σ : Equiv.Perm (Fin 5)}
    (hσ : σ.IsCycle ∧ σ.support.card = 5) :
    (GP_of_FeedForward hn F d u σ).computes (F.evalNode u) σ := by
  -- Apply the induction hypothesis to the previous layer's programs.
  have h_ind : ∀ (v : F.nodes d) (σ : Equiv.Perm (Fin 5)), σ.IsCycle ∧ σ.support.card = 5 → (GP_of_FeedForward hn F d v σ).computes (fun x => F.evalNode v x) σ := by
    induction' d using Fin.induction with d ih;
    · unfold GroupProgram.computes; aesop;
    · intro v σ hσ
      have h_layer : (GP_of_FeedForward_layer hn (F.gates d) (GP_of_FeedForward hn F d.castSucc) v σ).computes (fun x => (F.gates d v).eval (fun n => F.evalNode n x)) σ := by
        apply GP_of_FeedForward_layer_computes
        · exact fun v ↦ ih v v
        · exact hσ
        · exact h_gates d v
      convert h_layer using 1;
  exact h_ind u σ hσ

/--
The length of the constructed group program for a layer is at most 4 times the maximum length of the previous layer's programs.
-/
theorem GP_of_FeedForward_layer_len' {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_GPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (L : ℕ) (hL : 1 ≤ L)
    (h_prev : ∀ v σ, (prev_GPs v σ).len ≤ L)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) :
    (GP_of_FeedForward_layer hn gates prev_GPs u σ).len ≤ 4 * L :=
  GP_of_FeedForward_layer_len hn gates hL h_prev u σ

/-
The permutation (0 1 2 3 4) is a 5-cycle.
-/
def sigma_five_cycle : Equiv.Perm (Fin 5) :=
  finRotate 5

lemma sigma_five_cycle_is_cycle : sigma_five_cycle.IsCycle ∧ sigma_five_cycle.support.card = 5 := by
  simp +decide [Equiv.Perm.IsCycle]

lemma sigma_five_cycle_zero_ne_zero : sigma_five_cycle 0 ≠ 0 := by
  decide

lemma sigma_five_cycle_ne_one : sigma_five_cycle ≠ 1 := by
  decide

/--
Convert a CircuitFamily to a BPFamily using Barrington's construction for n > 0. For n=0,
return a trivial BP. For depth 0 circuits (n=1), return a variable BP.
-/
noncomputable def BPFamily_of_CircuitFamily {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out) : BPFamily (Fin 2) :=
  fun n ↦
    if hn : n = 0 then
      -- Trivial GP for n=0. Just evaluate and return that.
      { depth := 0
        nodes := fun _ ↦ Fin 1
        nodeVar := fun {k} _ ↦ k.elim0
        edges := fun {k} _ ↦ k.elim0
        startUnique := { default := 0, uniq := fun _ ↦ Fin.eq_zero _ }
        retVals := fun _ ↦ (CF 0).eval₁ (fun x ↦ x.elim0)
      }
    else
      let F := CF n
      let u : F.nodes (Fin.last F.depth) := cast F.nodes_last.symm (default : out)
      let GP := GP_of_FeedForward (Nat.pos_of_ne_zero hn) F _ u sigma_five_cycle
      GP.toBranchingProgram sigma_five_cycle (Fin 5)

/-
Partial evaluation of a group program using the first k instructions.
-/
def GroupProgram.eval_partial {n : ℕ} (GP : GroupProgram (Fin n) (Equiv.Perm (Fin 5))) (k : ℕ) (x : Fin n → Fin 2) : Equiv.Perm (Fin 5) :=
  ((List.finRange GP.len).take k).foldl (fun acc i ↦
    let p := if x (GP.var i) = 1 then GP.perm1 i else GP.perm0 i
    p * acc) 1

/-
Evaluation is equivalent to partial evaluation at the full length.
-/
theorem GroupProgram.eval_eq_eval_partial {n : ℕ} (GP : GroupProgram (Fin n) (Equiv.Perm (Fin 5))) (x : Fin n → Fin 2) :
    GP.eval x = GP.eval_partial GP.len x := by
  rw [eval_partial, List.take_of_length_le (by simp)]
  rfl

/-
The nodes at layer k > 0 in the converted branching program are Fin 5.
-/
lemma GroupProgram.toBranchingProgram_nodes_eq_fin5 {n : ℕ} (GP : GroupProgram (Fin n) (Equiv.Perm (Fin 5))) (σ : Equiv.Perm (Fin 5)) (k : ℕ) (hk : k ≤ GP.len) (hk0 : 0 < k) :
    (GP.toBranchingProgram σ (Fin 5)).nodes ⟨k, Nat.lt_succ_of_le hk⟩ = Fin 5 := by
  cases k <;> aesop

/-
The node reached at layer k in the converted branching program corresponds to the value of 0 under the partial evaluation of the Barrington program.
-/
theorem GroupProgram.toBranchingProgram_evalLayer_eq_eval_partial {n : ℕ} (GP : GroupProgram (Fin n) (Equiv.Perm (Fin 5))) (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) (k : ℕ) (hk : k ≤ GP.len) (hk0 : 0 < k) :
    cast (toBranchingProgram_nodes_eq_fin5 GP σ k hk hk0) ((GP.toBranchingProgram σ (Fin 5)).evalLayer ⟨k, Nat.lt_succ_of_le hk⟩ x) = (GP.eval_partial k x) 0 := by
  generalize_proofs at *;
  induction' k with k ih
  · simp_all
  cases k
  · rcases GP with ⟨ _ | _, _, _, _ ⟩
    · simp at hk
    · simp [eval_partial, List.finRange, toBranchingProgram]
      aesop
  · simp +contextual only at ih
    rename_i h₁ h₂ h₃
    specialize ih (by linarith) (by linarith) (by grind)
    unfold toBranchingProgram eval_partial at ih ⊢
    simp [LayeredBranchingProgram.evalLayer, LayeredBranchingProgram.start,
      Fin.inductionOn, Fin.induction, List.take_succ] at ih ⊢
    rw [List.getElem?_eq_getElem (by norm_num; linarith)]
    simp only [List.getElem_finRange, Fin.cast_mk, Option.elim_some]
    split_ifs with h
    · simp [Fin.induction.go] at ih ⊢
      simp [ih, h]
    · simp [Fin.induction.go] at ih ⊢
      simp [ih, h]

/-
The evaluation of the converted branching program is correct (assuming length > 0).
-/
theorem GroupProgram.toBranchingProgram_eval {n : ℕ} (GP : GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) (hσ : σ 0 ≠ 0):
    (GP.toBranchingProgram σ (Fin 5)).eval x = if (GP.eval x) 0 = σ 0 then 1 else 0 := by
  by_cases h_len : GP.len = 0
  · rcases GP with ⟨len, var, perm0, perm1⟩
    dsimp at h_len
    subst len
    simp [eval, toBranchingProgram, LayeredBranchingProgram.eval ]
    exact hσ.symm
  replace h_len : 0 < GP.len := by omega
  -- Since GP.len > 0, the last layer is at index GP.len. By definition of toGP, the nodes at this layer are Fin 5.
  have h_last_layer : (GP.toBranchingProgram σ (Fin 5)).nodes ⟨GP.len, Nat.lt_succ_self _⟩ = Fin 5 :=
    if_neg h_len.ne'
  -- By definition of toGP, the evaluation at the last layer is the result of applying the permutation σ to the value at 0.
  have h_eval_last_layer : (GP.toBranchingProgram σ (Fin 5)).eval x = if (cast h_last_layer ((GP.toBranchingProgram σ (Fin 5)).evalLayer ⟨GP.len, Nat.lt_succ_self _⟩ x)) = σ 0 then 1 else 0 := by
    unfold toBranchingProgram at *
    simp only [Nat.succ_eq_add_one, Fin.val_eq_zero_iff, Fin.coe_castSucc, Fin.isValue, ite_smul,
      Equiv.Perm.smul_def, Fin.val_succ, Nat.add_eq_zero, one_ne_zero, and_false, ↓dreduceIte, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, cast_eq, Fin.val_last, Lean.Elab.WF.paramLet]
    split
    · simp_all only [lt_self_iff_false]
    · dsimp at h_last_layer
      split_ifs
      · simp [LayeredBranchingProgram.eval]
        congr! 4
        grind
      · contradiction
  convert h_eval_last_layer using 2;
  rw [toBranchingProgram_evalLayer_eq_eval_partial]
  · rw [eval_eq_eval_partial]
  · rfl
  · exact h_len

theorem GroupProgram.of_CircuitFamily_IsOblivious {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out) :
    (BPFamily_of_CircuitFamily CF).IsOblivious := by
  intro n
  dsimp [BPFamily_of_CircuitFamily]
  split_ifs with hn
  <;> simp [toBranchingProgram, LayeredBranchingProgram.IsOblivious]
/-
The branching program family constructed from a circuit family has width at most 5.
-/
theorem GroupProgram.of_CircuitFamily_hasWidth_five {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out) :
    (BPFamily_of_CircuitFamily CF).hasWidth (·≤5) := by
  intro n
  dsimp [BPFamily_of_CircuitFamily]
  split_ifs with hn
  · simp [LayeredBranchingProgram.width]
  · apply width_toBranchingProgram

/-
If a circuit family has logarithmic depth, the constructed branching program family has polynomial depth.
-/
theorem GroupProgram.of_CircuitFamily_hasDepth_poly {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out)
    (h_depth : CF.hasDepth GrowthRate.log) :
    (BPFamily_of_CircuitFamily CF).hasDepth GrowthRate.poly := by
  apply GrowthRate.mono (f := fun n ↦ 4 ^ (CF n).depth)
  · refine GrowthRate.exp_comp_log ?_ h_depth
    exact ⟨4, by simpa using Asymptotics.isBigO_refl ..⟩
  · intro n
    dsimp [BPFamily_of_CircuitFamily]
    split_ifs
    · simp [*]
    · dsimp [toBranchingProgram] --make this step a lemma: f.toBranchingProgram.depth = f.len
      grw [GP_of_FeedForward_len]
      simp

theorem GroupProgram.of_CircuitFamily_computes {out : Type} [Unique out]
    {CF : CircuitFamily₁ (Fin 2) out} {f : FuncFamily₁ (Fin 2)}
    (hcf : CF.computes₁ f) (hcf_gates : CF.onlyUsesGates NC_GateOps):
    (BPFamily_of_CircuitFamily CF).computes f := by
  intro n
  rw [BPFamily_of_CircuitFamily]
  rcases n with _ | n
  · simp only [reduceDIte]
    unfold LayeredBranchingProgram.eval
    convert hcf 0
  rw [← hcf (n + 1)]
  simp
  generalize_proofs pf1 pf2
  have h := GP_of_FeedForward_computes pf1 (hcf_gates (n + 1)) (cast pf2 default) sigma_five_cycle_is_cycle
  unfold computes at h
  ext1 x
  rw [GroupProgram.toBranchingProgram_eval _ _ _ (by decide), h x]
  unfold eval₁
  split_ifs with h₁ h₂ h₂
  · simp_all
    symm
    assumption
  · simp_all
  · exfalso
    revert h₂; decide
  · symm
    contrapose! h₁
    exact Fin.eq_one_of_ne_zero _ h₁

instance GP_of_CircuitFamily_Finite {out : Type} [Unique out]
  (CF : CircuitFamily₁ (Fin 2) out) [CF.Finite] :
    (BPFamily_of_CircuitFamily CF).Finite := by
  constructor
  intro n
  dsimp [BPFamily_of_CircuitFamily]
  split_ifs with hn
  · constructor
    intro i
    simp
    infer_instance
  · constructor
    intro i
    -- Since Fin 5 is finite, any subtype of it is also finite.
    have h_subtype_finite : ∀ (i : Fin ((GP_of_FeedForward (Nat.pos_of_ne_zero hn) (CF n) (Fin.last (CF n).depth) (cast (CF n).nodes_last.symm Inhabited.default) sigma_five_cycle).toBranchingProgram sigma_five_cycle (Fin 5)).depth.succ), Finite (((GP_of_FeedForward (Nat.pos_of_ne_zero hn) (CF n) (Fin.last (CF n).depth) (cast (CF n).nodes_last.symm Inhabited.default) sigma_five_cycle).toBranchingProgram sigma_five_cycle (Fin 5)).nodes i) := by
      intro i
      by_cases hi : i = ⟨0, Nat.succ_pos _⟩
      · subst i
        change Finite (Fin 1)
        infer_instance
      · convert (Finite.of_fintype (Fin 5))
        apply GroupProgram.toBranchingProgram_nodes_eq_fin5
        · exact Nat.le_of_lt_succ i.2
        · exact Nat.pos_of_ne_zero (Fin.val_injective.ne hi)
    exact h_subtype_finite i

/--
If a group program computes a function f with permutation sigma, then its converted branching program computes f.
-/
theorem GroupProgram.toBranchingProgram_computes_of_computes {n : ℕ} (GP : GroupProgram (Fin n) (Equiv.Perm (Fin 5)))
    (f : (Fin n → Fin 2) → Fin 2) (σ : Equiv.Perm (Fin 5))
    (hσ0 : σ 0 ≠ 0) (h : GP.computes f σ) :
    (GP.toBranchingProgram σ (Fin 5)).computes f := by
  rw [LayeredBranchingProgram.computes]
  intro x
  rw [GroupProgram.toBranchingProgram_eval GP σ x hσ0]
  rcases Fin.exists_fin_two.mp ⟨f x, rfl⟩ with h₂ | h₂
  · simp [h x, h₂, hσ0.symm]
  · simp [h x, h₂]

theorem NC1_subset_BPClass_five : NCi 1 ⊆ BPClass (·≤5) .poly true := by
  intro f ⟨u, hu, cf, hcf⟩
  use BPFamily_of_CircuitFamily cf
  rcases hcf with ⟨hcf_fin, hcf_comp, _, hcf_depth, hcf_gates⟩
  fconstructor
  · apply GP_of_CircuitFamily_Finite
  and_intros
  · apply GroupProgram.of_CircuitFamily_computes hcf_comp hcf_gates
  · apply GroupProgram.of_CircuitFamily_hasWidth_five
  · apply GroupProgram.of_CircuitFamily_hasDepth_poly
    simp_rw [pow_one, GrowthRate.bigO_log2_eq_log] at hcf_depth
    exact hcf_depth
  · intro _
    apply GroupProgram.of_CircuitFamily_IsOblivious

section branchingProgramToCircuit

/- Define a circuit that computes the output of a branching program, to show that constant-width
branching programs can be computed in log-depth.

Start by defining the relevant gates in a one-hot encoding, then define the binary-division structure
of the circuit, then the circuit itself, and then prove correctness. This will give a circuit of
linear size in the input and depth log2(n) (up to an additive constant). The initial gates are not
all NC_GateOps, since they use gates of an arity greater than 2 for combining two one-hot encodings.

Later we'll show how to "compile" this circuit to use only arity-2 gates, with some constant increase
in size and depth.
-/


/-
Define the gate operations for matrix multiplication, base transitions, and the final output step.
MatrixMulOp combines two boolean matrices (represented by their rows/cols).
BaseOp computes the transition for a single step based on the input bit.
FinalOp computes the final output from the last layer's state.
-/
def MatrixMulOp (k : ℕ) : FeedForward.GateOp (Fin 2) where
  ι := Fin k ⊕ Fin k
  func x := if ∃ i, x (.inl i) = 1 ∧ x (.inr i) = 1 then 1 else 0

def BaseOp (b0 b1 : Fin 2) : FeedForward.GateOp (Fin 2) where
  ι := Fin 1
  func x := if x 0 = 0 then b0 else b1

def FinalOp (k : ℕ) (ret : Fin k → Fin 2) : FeedForward.GateOp (Fin 2) where
  ι := Fin k
  func x := if ∃ i, x i = 1 ∧ ret i = 1 then 1 else 0

/-
Define the height H of the circuit construction (log depth of BP) and the interval helper function.
H is the ceiling of log2 of the BP depth.
interval(t, j) returns the start and end layer indices for the j-th interval at level t of the recursive construction.
Corrected the proof term for Fin bounds.
-/
def BP_to_Circuit_H {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) : ℕ :=
  Nat.clog 2 BP.depth

def BP_to_Circuit_interval {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) (t j : ℕ) : Fin (BP.depth + 1) × Fin (BP.depth + 1) :=
  (⟨min BP.depth (j * 2^t), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩,
   ⟨min BP.depth ((j + 1) * 2^t), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩)

/-
Define the nodes of the circuit.
`LayerNodes` represents the nodes at a specific level `t` of the recursive construction (corresponding to layer `t+1` of the circuit). It consists of pairs of BP nodes for each interval at that level.
`Depth` is the total depth of the circuit (H + 2).
`Nodes` defines the type of nodes at each layer `k` of the circuit:
- Layer 0: Inputs (Fin n).
- Layer H+2: Output (Fin 1).
- Intermediate layers k: `LayerNodes` at level `k-1`.
-/
def BP_to_Circuit_LayerNodes {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) (t : ℕ) : Type :=
  Σ (j : Fin ⌈(BP.depth : ℚ) / 2^t⌉₊), BP.nodes (BP_to_Circuit_interval BP t j).1 × BP.nodes (BP_to_Circuit_interval BP t j).2

def BP_to_Circuit_Depth {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) : ℕ :=
  BP_to_Circuit_H BP + 2

def BP_to_Circuit_Nodes {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) (k : Fin (BP_to_Circuit_Depth BP + 1)) : Type :=
  if k = 0 then Fin n
  else if k = Fin.last (BP_to_Circuit_Depth BP) then Fin 1
  else BP_to_Circuit_LayerNodes BP (k - 1)

/-
Define a constant gate operation.
-/
def ConstOp (b : Fin 2) : FeedForward.GateOp (Fin 2) where
  ι := Fin 0
  func _ := b

/-
Define the gates for the first layer (layer 0 to 1) of the circuit.
These gates correspond to the base intervals of length 1 (or 0) in the branching program.
If the interval is valid (j < depth), the gate checks if the input variable matches the edge required to go from u_start to u_end.
If the interval is invalid (j >= depth), the gate outputs 1 iff u_start == u_end (identity path of length 0).
Using `sorry` for proofs to avoid type errors and `open Classical` for decidability.
-/
open Classical in
def BP_to_Circuit_Gates_0 {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2))
    (u : BP_to_Circuit_LayerNodes BP 0) : FeedForward.Gate (Fin 2) (Fin n) :=
  let j := u.1
  let u_start := u.2.1
  let u_end := u.2.2
  if h : j.val < BP.depth then
    let k : Fin BP.depth := ⟨j.val, h⟩
    let u_start_casted : BP.nodes k.castSucc := cast (by
    -- By definition of `BP_to_Circuit_interval`, the first component is `min BP.depth (j * 2^0)`, which simplifies to `j` since `2^0 = 1`.
    simp [BP_to_Circuit_interval];
    -- Since $j$ is a Fin, its value is less than $BP.depth$, so $min BP.depth j.val$ is just $j.val$.
    have h_min : min BP.depth j.val = j.val := by
      exact min_eq_right h.le;
    convert rfl;
    exact h_min.symm) u_start
    let var := BP.nodeVar u_start_casted
    let edge0 : BP.nodes k.succ := BP.edges u_start_casted 0
    let edge1 : BP.nodes k.succ := BP.edges u_start_casted 1
    let u_end_casted : BP.nodes k.succ := cast (by
    -- By definition of `BP_to_Circuit_interval`, the second component is `min(BP.depth, (j + 1) * 2^0)`.
    simp [BP_to_Circuit_interval];
    congr;
    exact min_eq_right ( Nat.succ_le_of_lt h )) u_end
    let b0 := if edge0 = u_end_casted then 1 else 0
    let b1 := if edge1 = u_end_casted then 1 else 0
    { op := BaseOp b0 b1
      inputs := fun _ ↦ var }
  else
    let u_start_casted : BP.nodes (Fin.last BP.depth) := cast (by
    -- Since $j \geq \text{depth}$, the first index of the interval is $j * 2^0 = j$, and since $j \geq \text{depth}$, this index is $\text{depth}$.
    have h_index : (BP_to_Circuit_interval BP 0 j.val).1.val = BP.depth := by
      exact min_eq_left ( by aesop );
    convert rfl;
    exact Fin.ext h_index.symm) u_start
    let u_end_casted : BP.nodes (Fin.last BP.depth) := cast (by
    congr! 1
    generalize_proofs at *;
    -- Since $j.val \geq BP.depth$, we have $1 + j.val \geq BP.depth + 1$, and thus $\min(BP.depth, 1 + j.val) = BP.depth$.
    have h_min : min BP.depth (1 + j.val) = BP.depth := by
      grind
    generalize_proofs at *;
    -- Since $j.val \geq BP.depth$, we have $1 + j.val \geq BP.depth + 1$, and thus $\min(BP.depth, 1 + j.val) = BP.depth$. Therefore, the second component of the interval is Fin.last BP.depth.
    simp [BP_to_Circuit_interval];
    exact Fin.ext ( by simpa [ add_comm ] using h_min )) u_end
    let b := if u_start_casted = u_end_casted then 1 else 0
    { op := ConstOp b
      inputs := fun i ↦ i.elim0 }

/-
Define the midpoint index for the interval splitting.
The midpoint of the interval at level `t+1` (which covers `j * 2^(t+1)` to `(j+1) * 2^(t+1)`) is `(2*j+1) * 2^t`.
We take the minimum with `BP.depth` to ensure it's a valid layer index.
-/
def BP_to_Circuit_midpoint {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) (t j : ℕ) : Fin (BP.depth + 1) :=
  ⟨min BP.depth ((2 * j + 1) * 2 ^ t), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

/-
Helper lemma: If `j` is a valid interval index at level `t+1`, then `2*j` is a valid interval index at level `t`.
This corresponds to the left child in the recursive construction of the circuit.
The number of intervals at level `t` is `ceil(depth / 2^t)`.
We need to show `2*j < ceil(depth / 2^t)` given `j < ceil(depth / 2^(t+1))`.
-/
lemma BP_to_Circuit_left_child_valid {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {t : ℕ} {j : ℕ} (h : j < ⌈(BP.depth : ℚ) / 2^(t+1)⌉₊) :
    2 * j < ⌈(BP.depth : ℚ) / 2^t⌉₊ := by
  rw [ Nat.lt_ceil, lt_div_iff₀ ] at * <;> norm_cast at *;
  · convert h using 1 ; ring;
  · positivity;
  · positivity

/-
Define helper lemmas to simplify the casts in `BP_to_Circuit_Gates_mid`.
These lemmas establish the relationships between the interval endpoints and the midpoint for the recursive step.
1. The start of interval `j` at level `t+1` is the same as the start of interval `2*j` at level `t`.
2. The midpoint of interval `j` at level `t+1` is the end of interval `2*j` at level `t`.
3. The midpoint of interval `j` at level `t+1` is the start of interval `2*j+1` at level `t`.
4. The end of interval `j` at level `t+1` is the same as the end of interval `2*j+1` at level `t`.
-/
lemma BP_to_Circuit_interval_start_eq_left_start {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {t j : ℕ} :
    (BP_to_Circuit_interval BP (t + 1) j).1 = (BP_to_Circuit_interval BP t (2 * j)).1 := by
  unfold BP_to_Circuit_interval; ring_nf

lemma BP_to_Circuit_interval_mid_eq_left_end {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {t j : ℕ} :
    BP_to_Circuit_midpoint BP t j = (BP_to_Circuit_interval BP t (2 * j)).2 := by
  rfl

lemma BP_to_Circuit_interval_mid_eq_right_start {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {t j : ℕ} :
    BP_to_Circuit_midpoint BP t j = (BP_to_Circuit_interval BP t (2 * j + 1)).1 := by
  rfl

lemma BP_to_Circuit_interval_end_eq_right_end {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {t j : ℕ} :
    (BP_to_Circuit_interval BP (t + 1) j).2 = (BP_to_Circuit_interval BP t (2 * j + 1)).2 := by
  unfold BP_to_Circuit_interval; ring_nf

/-
Define the matrix multiplication gate construction for the intermediate layers.
This helper function constructs the gate when the right child interval is valid.
It uses `MatrixMulOp` to combine the results from the left and right sub-intervals.
The inputs to the gate are the values corresponding to the paths through the midpoint.
Using helper lemmas for interval bounds and equality.
-/
open Classical in
def BP_to_Circuit_Gates_mid_Matrix {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) [BP.Finite]
    (t : Fin (BP_to_Circuit_H BP))
    (u : BP_to_Circuit_LayerNodes BP (t.val + 1))
    (h_right : 2 * u.1.val + 1 < ⌈(BP.depth : ℚ) / 2^t.val⌉₊) :
    FeedForward.Gate (Fin 2) (BP_to_Circuit_LayerNodes BP t.val) :=
  let j := u.1
  let u_start := u.2.1
  let u_end := u.2.2
  let mid_idx := BP_to_Circuit_midpoint BP t.val j.val
  let mid_nodes := BP.nodes mid_idx
  let k := Nat.card mid_nodes
  let equiv : Fin k ≃ mid_nodes := (Finite.equivFin mid_nodes).symm
  { op := MatrixMulOp k
    inputs := fun i ↦
      match i with
      | .inl i =>
        let v := equiv i
        let node : BP_to_Circuit_LayerNodes BP t.val :=
          ⟨⟨2 * j.val, BP_to_Circuit_left_child_valid j.2⟩, ⟨cast (by
          -- By definition of `BP_to_Circuit_interval`, the start of the interval at level `t+1` is the same as the start of the interval at level `t` for `2*j`.
          apply congr_arg (fun x => BP.nodes x) (BP_to_Circuit_interval_start_eq_left_start)) u_start, cast (by
          exact rfl) v⟩⟩
        node
      | .inr i =>
        let v := equiv i
        let node : BP_to_Circuit_LayerNodes BP t.val :=
          ⟨⟨2 * j.val + 1, h_right⟩, ⟨cast (by
          -- By definition of `BP_to_Circuit_midpoint`, we know that `mid_idx` is equal to `BP_to_Circuit_interval BP t (2 * j + 1).1`.
          have h_mid_eq : mid_idx = (BP_to_Circuit_interval BP t (2 * j + 1)).1 := by
            -- By definition of `BP_to_Circuit_midpoint`, we know that `mid_idx` is equal to the start of the interval at level `t` for `2 * j + 1`.
            apply BP_to_Circuit_interval_mid_eq_right_start;
          exact h_mid_eq ▸ rfl) v, cast (by
          -- By definition of `BP_to_Circuit_interval`, we know that the second element of the pair for `t + 1` is equal to the second element of the pair for `t` with `2 * j + 1`.
          apply congr_arg BP.nodes
          apply BP_to_Circuit_interval_end_eq_right_end) u_end⟩⟩
        node
  }

/-
Lemma: If the right child interval is invalid (index out of bounds), then the end of the parent interval is equal to the end of the left child interval.
This is because both intervals extend to the end of the branching program (depth D).
Proof uses the fact that the index bound implies the start of the right child (which is the end of the left child) is beyond the depth D.
-/
lemma BP_to_Circuit_interval_end_eq_left_end_of_right_invalid {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {t j : ℕ} (h : ¬ (2 * j + 1 < ⌈(BP.depth : ℚ) / 2^t⌉₊)) :
    (BP_to_Circuit_interval BP (t + 1) j).2 = (BP_to_Circuit_interval BP t (2 * j)).2 := by
      have := @BP_to_Circuit_interval_end_eq_right_end;
      convert this using 1;
      simp [ BP_to_Circuit_interval ];
      rw [ min_eq_left, min_eq_left ] <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
      · rw [ div_le_iff₀ ] at h <;> norm_cast at * <;> linarith [ Nat.one_le_pow t 2 zero_lt_two ];
      · rw [ div_le_iff₀ ] at h <;> norm_cast at * ; linarith [ Nat.one_le_pow t 2 zero_lt_two ]

/-
Define the identity gate construction for the intermediate layers.
This helper function constructs the gate when the right child interval is invalid.
In this case, the interval is identical to the left child interval, so we just propagate the result using an identity gate.
Using `BP_to_Circuit_left_child_valid` for the left child index.
Using `BP_to_Circuit_interval_start_eq_left_start` and `BP_to_Circuit_interval_end_eq_left_end_of_right_invalid` for casts.
-/
open Classical in
def BP_to_Circuit_Gates_mid_Identity {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2))
    (t : Fin (BP_to_Circuit_H BP))
    (u : BP_to_Circuit_LayerNodes BP (t.val + 1))
    (h_right_invalid : ¬ (2 * u.1.val + 1 < ⌈(BP.depth : ℚ) / 2^t.val⌉₊)) :
    FeedForward.Gate (Fin 2) (BP_to_Circuit_LayerNodes BP t.val) :=
  let j := u.1
  let u_start := u.2.1
  let u_end := u.2.2
  let left_idx : Fin ⌈(BP.depth : ℚ) / 2^t.val⌉₊ := ⟨2 * j.val, BP_to_Circuit_left_child_valid j.2⟩
  let node : BP_to_Circuit_LayerNodes BP t.val :=
    ⟨left_idx, ⟨cast (by
      apply congr_arg BP.nodes
      apply BP_to_Circuit_interval_start_eq_left_start) u_start,
      cast (by
      apply congr_arg BP.nodes
      apply BP_to_Circuit_interval_end_eq_left_end_of_right_invalid h_right_invalid) u_end⟩⟩
  { op := FeedForward.GateOp.id (Fin 2)
    inputs := fun _ ↦ node }

/-
Define the gate construction for the intermediate layers by dispatching to the helper functions.
If the right child interval is valid, use the matrix multiplication gate.
Otherwise, use the identity gate.
-/
open Classical in
def BP_to_Circuit_Gates_mid {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) [BP.Finite]
    (t : Fin (BP_to_Circuit_H BP))
    (u : BP_to_Circuit_LayerNodes BP (t.val + 1)) :
    FeedForward.Gate (Fin 2) (BP_to_Circuit_LayerNodes BP t.val) :=
  if h : 2 * u.1.val + 1 < ⌈(BP.depth : ℚ) / 2^t.val⌉₊ then
    BP_to_Circuit_Gates_mid_Matrix BP t u h
  else
    BP_to_Circuit_Gates_mid_Identity BP t u h

/-
Prove that `BP_to_Circuit_LayerNodes` is finite.
This is needed for `Fintype.ofFinite` in the gate definitions.
It follows from the finiteness of `Fin`, `BP.nodes`, and the closure of finite types under Sigma and Prod.
-/
instance BP_to_Circuit_LayerNodes_Finite {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) [BP.Finite] (t : ℕ) :
    Finite (BP_to_Circuit_LayerNodes BP t) := by
  dsimp [BP_to_Circuit_LayerNodes]
  infer_instance

/-
Define the final gate of the circuit.
This gate takes all nodes from the top level of the tree (level H) as input.
It outputs 1 if there exists a node `(u, v)` such that `u` is the start node, `v` is an accepting node (retVal = 1), and the circuit computed 1 for `(u, v)` (meaning there is a path).
Using `FinalOp` with a `ret` function that checks these conditions.
Using `sorry` for casts (since `BP.start` is in `nodes 0` and `u_start` is in `nodes (interval ...).1`, etc).
Now that `BP_to_Circuit_LayerNodes_Finite` is defined, `Fintype.ofFinite` should work.
-/
open Classical in
def BP_to_Circuit_Gates_last {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) [BP.Finite]
    : FeedForward.Gate (Fin 2) (BP_to_Circuit_LayerNodes BP (BP_to_Circuit_H BP)) :=
  let nodes := BP_to_Circuit_LayerNodes BP (BP_to_Circuit_H BP)
  letI := Fintype.ofFinite nodes
  let k := Nat.card nodes
  let equiv : Fin k ≃ nodes := (Finite.equivFin nodes).symm
  let ret : Fin k → Fin 2 := fun i ↦
    let node := equiv i
    let u_start := node.2.1
    let u_end := node.2.2
    if u_start = cast (by
    -- Since the interval at level H is just the entire depth, the start of the interval is 0.
    have h_interval_start : (BP_to_Circuit_interval BP (BP_to_Circuit_H BP) node.fst).1 = 0 := by
      norm_num [ BP_to_Circuit_interval ];
      exact Or.inr ( Nat.eq_zero_of_le_zero ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt node.fst, show node.fst.val < 1 from Nat.lt_succ_of_le ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt node.fst, show ⌈ ( BP.depth : ℚ ) / 2 ^ BP_to_Circuit_H BP⌉₊ ≤ 1 from by
                                                                                                                                                                                                          simp +zetaDelta at *;
                                                                                                                                                                                                          rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ Nat.le_log_iff_pow_le, BP_to_Circuit_H ];
                                                                                                                                                                                                          exact_mod_cast Nat.le_pow_clog ( by decide ) _ ] ) ) ] ) ) );
    rw [h_interval_start]) BP.start ∧ BP.retVals (cast (by
    refine' congr_arg BP.nodes ( Fin.ext _ );
    simp [ BP_to_Circuit_H, BP_to_Circuit_interval ];
    -- By definition of `Nat.clog`, we know that `2 ^ Nat.clog 2 BP.depth ≥ BP.depth`.
    have h_exp : 2 ^ Nat.clog 2 BP.depth ≥ BP.depth := by
      exact_mod_cast Nat.le_pow_clog ( by decide ) _;
    exact le_trans h_exp ( Nat.le_trans ( by norm_num ) ( Nat.mul_le_mul ( Nat.succ_le_succ ( Nat.zero_le _ ) ) le_rfl ) )) u_end) = 1 then 1 else 0
  { op := FinalOp k ret
    inputs := fun i ↦ equiv i }

/-
Define the full circuit construction from the branching program.
The circuit has depth `H + 2`.
Layer 0 gates are `BP_to_Circuit_Gates_0`.
Layer `H + 1` gates are `BP_to_Circuit_Gates_last`.
Intermediate layers `d` (corresponding to tree level `t = d - 1`) use `BP_to_Circuit_Gates_mid`.
-/
open Classical in
def BP_to_Circuit {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) [BP.Finite] :
    FeedForward (Fin 2) (Fin n) (Fin 1) :=
  { depth := BP_to_Circuit_Depth BP
    nodes := BP_to_Circuit_Nodes BP
    gates := fun d u ↦
      if h0 : d.val = 0 then
        let u' : BP_to_Circuit_LayerNodes BP 0 := cast (by
        cases d ; aesop) u
        let g := BP_to_Circuit_Gates_0 BP u'
        { op := g.op, inputs := fun i ↦ cast (by
            -- Since `d` is 0, `d.castSucc` is also 0. Therefore, `BP_to_Circuit_Nodes BP d.castSucc` is the same as `BP_to_Circuit_Nodes BP 0`, which is `Fin n`.
            simp [BP_to_Circuit_Nodes, h0];
            -- Since $d.castSucc = 0$, the implication holds trivially because the antecedent is false.
            intro h_castSucc_ne_zero
            exfalso
            apply h_castSucc_ne_zero
            simp [Fin.ext_iff, h0]) (g.inputs i) }
      else if h_last : d.val = BP_to_Circuit_H BP + 1 then
        let u' : Fin 1 := cast (by
        -- Since `d` is at the last layer, `d.val = BP_to_Circuit_H BP + 1`, so `BP_to_Circuit_Nodes BP d.succ` is `Fin 1` by definition.
        have h_last_node : d.succ = Fin.last (BP_to_Circuit_Depth BP) := by
          ext ; simp [ h_last, Fin.last ];
          exact rfl;
        -- Substitute `h_last_node` into the definition of `BP_to_Circuit_Nodes`.
        rw [h_last_node];
        -- By definition of BP_to_Circuit_Nodes, when the input is the last element, it returns Fin 1.
        simp [BP_to_Circuit_Nodes];
        exact fun h => absurd h ( Nat.ne_of_gt ( Nat.succ_pos _ ) )) u
        let g := BP_to_Circuit_Gates_last BP
        { op := g.op, inputs := fun i ↦ cast (by
            -- By definition of `BP_to_Circuit_Nodes`, when `d = BP_to_Circuit_H BP + 1`, the nodes are `BP_to_Circuit_LayerNodes BP (BP_to_Circuit_H BP)`.
            simp [BP_to_Circuit_Nodes, h_last];
            simp [ Fin.ext_iff ];
            -- Since $d \neq 0$, the implication holds trivially.
            intro h
            exfalso
            exact h0 h) (g.inputs i) }
      else
        let t : Fin (BP_to_Circuit_H BP) := ⟨d.val - 1, by
          -- Since $d$ is a Fin (BP_to_Circuit_Depth BP), its value is between 0 and BP_to_Circuit_Depth BP - 1. Therefore, $d.val - 1$ is between 0 and BP_to_Circuit_H BP + 1 - 2, which simplifies to BP_to_Circuit_H BP - 1.
          have h_bounds : d.val < BP_to_Circuit_H BP + 2 := by
            exact lt_of_lt_of_le d.2 ( Nat.le_refl _ );
          omega⟩
        let u' : BP_to_Circuit_LayerNodes BP (t.val + 1) := cast (by
        -- By definition of `BP_to_Circuit_Nodes`, we know that `BP_to_Circuit_Nodes BP d.succ` is equal to `BP_to_Circuit_LayerNodes BP (d.val - 1)` because `d.val` is the index of the layer.
        simp [BP_to_Circuit_Nodes];
        -- Since `d.succ` cannot be the last element, the if statement simplifies to `BP_to_Circuit_LayerNodes BP d.val`.
        have h_if_false : d.succ ≠ Fin.last (BP_to_Circuit_Depth BP) := by
          simp [ Fin.ext_iff];
          exact Nat.add_one_ne_add_one_iff.mpr h_last
        simp [h_if_false];
        exact congr_arg _ ( by rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr h0 ) ] )) u
        let g := BP_to_Circuit_Gates_mid BP t u'
        { op := g.op, inputs := fun i ↦ cast (by
            -- By definition of `BP_to_Circuit_Nodes`, we know that `BP_to_Circuit_Nodes BP d.castSucc` is equal to `BP_to_Circuit_LayerNodes BP t.val` because `d.castSucc` is the previous layer.
            simp [BP_to_Circuit_Nodes];
            -- Since `d` is not zero, the if statement simplifies to the else part.
            simp [Fin.ext_iff, h0];
            -- Since `t` is defined as `⟨d.val - 1, by sorry⟩`, we have `t.val = d.val - 1`.
            simp [t]) (g.inputs i) }
    nodes_zero := by
      -- By definition of `BP_to_Circuit_Nodes`, for `k = 0`, it returns `Fin n`.
      simp [BP_to_Circuit_Nodes]
    nodes_last := by
      -- By definition of `BP_to_Circuit_Nodes`, when `k = Fin.last (BP_to_Circuit_Depth BP)`, it returns `Fin 1`.
      simp [BP_to_Circuit_Nodes, BP_to_Circuit_Depth]
  }

/-
Prove that the depth of the constructed circuit is `ceil(log2(BP.depth)) + 2`.
This follows directly from the definition of `BP_to_Circuit` and `BP_to_Circuit_Depth`.
-/
theorem BP_to_Circuit_depth_eq {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) [BP.Finite] :
    (BP_to_Circuit BP).depth = Nat.clog 2 BP.depth + 2 := by
  simp [BP_to_Circuit, BP_to_Circuit_Depth, BP_to_Circuit_H]

/-
Define `BP_evalSegment` which evaluates the branching program from layer `i` to layer `j` starting at node `u`.
If `i = j`, it returns `u`.
Otherwise, it steps one layer forward and recurses.
Using `termination_by j.val - i.val` to avoid `Fin` subtraction issues.
Explicitly constructing proofs for bounds and casts.
-/
def BP_evalSegment {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2))
    (x : Fin n → Fin 2) (i j : Fin (BP.depth + 1)) (h : i ≤ j) (u : BP.nodes i) : BP.nodes j :=
  if h_eq : i = j then
    cast (by rw [h_eq]) u
  else
    let i_val_lt_j_val : i.val < j.val := lt_of_le_of_ne h (Fin.val_injective.ne h_eq)
    let i_lt_depth : i.val < BP.depth := lt_of_lt_of_le i_val_lt_j_val (Nat.le_of_lt_succ j.isLt)
    let i' : Fin BP.depth := ⟨i.val, i_lt_depth⟩
    let u_casted : BP.nodes i'.castSucc := cast (by
      apply congr_arg BP.nodes
      apply Fin.ext
      simp [i']) u
    let next_u := BP.edges u_casted (x (BP.nodeVar u_casted))
    BP_evalSegment BP x i'.succ j (by
      apply Nat.succ_le_of_lt
      exact i_val_lt_j_val) next_u
termination_by j.val - i.val
decreasing_by
  simp_wf
  exact Nat.sub_succ_lt_self j.val i.val i_val_lt_j_val

/-
Lemma: `BP_evalSegment` for a single step (from `i` to `i+1`) is equivalent to `BP.edges`.
This simplifies the reasoning for the base case of the circuit correctness.
-/
lemma BP_evalSegment_step {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2))
    (x : Fin n → Fin 2) (i : Fin BP.depth) (u : BP.nodes i.castSucc) :
    BP_evalSegment BP x i.castSucc i.succ (Nat.le_succ _) u =
    BP.edges u (x (BP.nodeVar u)) := by
      -- By definition of `BP_evalSegment`, when `i = j`, it returns `u`.
      simp [BP_evalSegment];
      exact fun h => absurd h ( ne_of_lt ( Fin.castSucc_lt_succ i ) )

/-
Lemma: The start of an interval is less than or equal to the end of the interval.
This is needed to satisfy the precondition of `BP_evalSegment`.
-/
lemma BP_to_Circuit_interval_le {n : ℕ} (BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)) (t j : ℕ) :
    (BP_to_Circuit_interval BP t j).1 ≤ (BP_to_Circuit_interval BP t j).2 := by
      exact min_le_min ( Nat.le_refl _ ) ( Nat.mul_le_mul_right _ ( by linarith ) )

/-
Lemma: When `j < depth`, the interval at level 0 is `(j, j+1)`.
This simplifies the interval expressions in the correctness proof.
Corrected the proof term for the upper bound of the interval end.
-/
lemma BP_to_Circuit_interval_0_lt {n : ℕ} {BP : LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2)}
    {j : Fin ⌈(BP.depth : ℚ) / 2^0⌉₊} (h : j.val < BP.depth) :
    BP_to_Circuit_interval BP 0 j.val = (⟨j.val, lt_trans h (Nat.lt_succ_self _)⟩, ⟨j.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt h)⟩) := by
      generalize_proofs at *;
      (generalize_proofs at *; simp_all [ BP_to_Circuit_interval ];);
      exact ⟨ Nat.le_of_lt h, Nat.le_of_lt_succ ‹_› ⟩
