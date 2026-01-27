
import CircuitComp.NC
import CircuitComp.BranchingProgram.Basic

import Mathlib.GroupTheory.SpecificGroups.Alternating

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}

open LayeredBranchingProgram

/-
Define BarringtonProgram and its evaluation.
-/
structure BarringtonProgram (n : ℕ) where
  len : ℕ
  var : Fin len → Fin n
  perm0 : Fin len → Equiv.Perm (Fin 5)
  perm1 : Fin len → Equiv.Perm (Fin 5)

namespace BarringtonProgram

def eval {n : ℕ} (BP : BarringtonProgram n) (x : Fin n → Fin 2) : Equiv.Perm (Fin 5) :=
  (List.finRange BP.len).foldl (fun acc i ↦
    let p := if x (BP.var i) = 1 then BP.perm1 i else BP.perm0 i
    p * acc) 1

def computes {n : ℕ} (BP : BarringtonProgram n) (f : (Fin n → Fin 2) → Fin 2) (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ ≠ 1 ∧ ∀ x, BP.eval x = if f x = 1 then σ else 1

/-
Define the nodes for the converted branching program. Layer 0 has 1 node, others have 5.
-/
def toBP_nodes {n : ℕ} (BP : BarringtonProgram n) (i : Fin (BP.len + 1)) : Type :=
  if i.val = 0 then Fin 1 else Fin 5

/-
Define the conversion from a Barrington Program to a Layered Branching Program. Explicitly handle types to avoid ambiguity.
-/
def toBP {n : ℕ} (BP : BarringtonProgram n) (σ : Equiv.Perm (Fin 5)) :
    LayeredBranchingProgram (Fin n) (Fin 2) (Fin 2) where
  depth := BP.len
  nodes := BP.toBP_nodes
  nodeVar := fun {k} _ ↦ BP.var k
  edges := fun {k} u b ↦
    if hk : k.val = 0 then
      let p := if b = 1 then BP.perm1 k else BP.perm0 k
      let dest : Fin 5 := p 0
      cast (by unfold toBP_nodes; aesop) dest
    else
      let u' : Fin 5 := cast (by simp [toBP_nodes, hk]) u
      let p := if b = 1 then BP.perm1 k else BP.perm0 k
      p u'
  startUnique := {
    default := cast (by simp [toBP_nodes]) (0 : Fin 1)
    uniq := fun x ↦ Fin.eq_zero _
  }
  retVals := fun u ↦
    if h : BP.len = 0 then
      0
    else
      let u' : Fin 5 := cast (by simp [toBP_nodes, h]) u
      if u' = σ 0 then 1 else 0

/-
The width of the converted branching program is at most 5.
-/
theorem width_toBP {n : ℕ} (BP : BarringtonProgram n) (σ : Equiv.Perm (Fin 5)) : (BP.toBP σ).width ≤ 5 := by
  apply ciSup_le
  unfold toBP toBP_nodes
  aesop

/-
Define the concatenation of two Barrington programs and prove that the evaluation of the concatenated program is the product of the evaluations (note the order due to function composition/multiplication convention).
-/
def append {n : ℕ} (BP1 BP2 : BarringtonProgram n) : BarringtonProgram n :=
  { len := BP1.len + BP2.len
    var := Fin.append BP1.var BP2.var
    perm0 := Fin.append BP1.perm0 BP2.perm0
    perm1 := Fin.append BP1.perm1 BP2.perm1
  }

theorem len_append {n : ℕ} (BP1 BP2 : BarringtonProgram n) : (append BP1 BP2).len = BP1.len + BP2.len :=
  rfl

theorem eval_append {n : ℕ} (BP1 BP2 : BarringtonProgram n) (x : Fin n → Fin 2) :
    (BP1.append BP2).eval x = BP2.eval x * BP1.eval x := by
  unfold append eval;
  rw [ show List.finRange ( BP1.len + BP2.len ) = List.map ( fun i => Fin.castAdd BP2.len i ) ( List.finRange BP1.len ) ++ List.map ( fun i => Fin.natAdd BP1.len i ) ( List.finRange BP2.len ) from ?_, List.foldl_append ];
  · simp [ Fin.append, List.foldl_map ];
    induction' ( List.finRange BP2.len ) using List.reverseRecOn with l ih <;> aesop;
  · refine' List.ext_get _ _ <;> simp
    intro i hi₁ hi₂; by_cases hi₃ : i < BP1.len <;> simp_all [Fin.castAdd ] ;

/-
Define the reverse of a Barrington program and prove that its evaluation is the inverse of the original program's evaluation.
-/
def reverse {n : ℕ} (BP : BarringtonProgram n) : BarringtonProgram n where
  len := BP.len
  var := BP.var ∘ Fin.rev
  perm0 := fun i ↦ (BP.perm0 (Fin.rev i))⁻¹
  perm1 := fun i ↦ (BP.perm1 (Fin.rev i))⁻¹

theorem eval_reverse {n : ℕ} (BP : BarringtonProgram n) (x : Fin n → Fin 2) :
    BP.reverse.eval x = (BP.eval x)⁻¹ := by
  unfold eval reverse
  -- By definition of `List.finRange`, we can rewrite the left-hand side to match the right-hand side.
  have h_finRange : List.finRange BP.len = List.map (fun i => Fin.rev i) (List.finRange BP.len).reverse := by
    refine' List.ext_get _ _ <;> simp [ Fin.rev ];
    exact fun i hi => by omega;
  conv_rhs => rw [ h_finRange ];
  induction' ( List.finRange BP.len ) using List.reverseRecOn with i _ ih <;> simp [ * ];
  split_ifs <;> simp_all +singlePass [ List.foldr_map];
  · induction i <;> simp [ * ];
    split_ifs <;> simp_all [ Equiv.Perm.ext_iff ];
  · induction i <;> simp [ * ];
    split_ifs <;> simp_all [ mul_assoc, inv_mul_eq_iff_eq_mul ]

/-
Define a Barrington program for a single variable and prove it computes the variable.
-/
def ofVar {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) : BarringtonProgram n where
  len := 1
  var := fun _ ↦ i
  perm0 := fun _ ↦ 1
  perm1 := fun _ ↦ σ

theorem eval_ofVar {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) :
    (BarringtonProgram.ofVar i σ).eval x = if x i = 1 then σ else 1 := by
  unfold ofVar; aesop;

/-
Define a constant Barrington program (reading a dummy variable) and prove it evaluates to the constant permutation.
-/
def const {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) : BarringtonProgram n where
  len := 1
  var := fun _ ↦ i
  perm0 := fun _ ↦ σ
  perm1 := fun _ ↦ σ

theorem eval_const {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) :
    (BarringtonProgram.const i σ).eval x = σ := by
  simp [eval, const, Fin.isValue, ite_self, List.finRange_succ]

/-
Define the commutator of two Barrington programs and prove its length is twice the sum of the lengths of the original programs.
-/
def commutator {n : ℕ} (BP1 BP2 : BarringtonProgram n) : BarringtonProgram n :=
  (BP1.append BP2).append (BP1.reverse.append BP2.reverse)

theorem len_commutator {n : ℕ} (BP1 BP2 : BarringtonProgram n) :
    (BP1.commutator BP2).len = 2 * BP1.len + 2 * BP2.len := by
  simp +arith [commutator, len_append, reverse]

/-
Prove that the evaluation of the commutator program is the commutator of the evaluations.
-/
theorem eval_commutator {n : ℕ} (BP1 BP2 : BarringtonProgram n) (x : Fin n → Fin 2) :
    (BP1.commutator BP2).eval x = (BP2.eval x)⁻¹ * (BP1.eval x)⁻¹ * BP2.eval x * BP1.eval x := by
  unfold commutator;
  rw [eval_append, eval_append, eval_append, eval_reverse, eval_reverse]
  group

/-
Prove that any 5-cycle in $S_5$ can be written as a commutator of two 5-cycles.
-/
theorem _root_.exists_commutator_eq_cycle (σ : Equiv.Perm (Fin 5)) (hσ : σ.IsCycle ∧ σ.support.card = 5) :
    ∃ α β : Equiv.Perm (Fin 5),
      α.IsCycle ∧ α.support.card = 5 ∧
      β.IsCycle ∧ β.support.card = 5 ∧
      σ = α * β * α⁻¹ * β⁻¹ := by
  revert σ
  simp [Equiv.Perm.IsCycle];
  native_decide +revert

/-
Prove that `ofVar` computes the projection function.
-/
theorem computes_ofVar {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) (hσ : σ ≠ 1) :
    (BarringtonProgram.ofVar i σ).computes (fun x ↦ x i) σ := by
  unfold computes; aesop

/-
Prove that the commutator of two Barrington programs computes the AND of their functions, given that the resulting commutator permutation is non-identity.
-/
theorem computes_and {n : ℕ} (BP1 BP2 : BarringtonProgram n)
    (f g : (Fin n → Fin 2) → Fin 2) (α β : Equiv.Perm (Fin 5))
    (h1 : BP1.computes f α) (h2 : BP2.computes g β)
    (h_comm : β⁻¹ * α⁻¹ * β * α ≠ 1) :
    (BP1.commutator BP2).computes (fun x ↦ f x * g x) (β⁻¹ * α⁻¹ * β * α) := by
  unfold computes at *
  refine ⟨h_comm, fun x ↦ ?_⟩
  simp [ *, BarringtonProgram.eval_commutator ]
  split_ifs <;> simp_all [ mul_assoc ]
  grind

/-
Define the conjugate of a Barrington program and prove its evaluation property.
-/
def conjugate {n : ℕ} (BP : BarringtonProgram n) (ρ : Equiv.Perm (Fin 5)) : BarringtonProgram n where
  len := BP.len
  var := BP.var
  perm0 := fun i ↦ ρ * BP.perm0 i * ρ⁻¹
  perm1 := fun i ↦ ρ * BP.perm1 i * ρ⁻¹

theorem eval_conjugate {n : ℕ} (BP : BarringtonProgram n) (ρ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) :
    (BP.conjugate ρ).eval x = ρ * BP.eval x * ρ⁻¹ := by
  unfold BarringtonProgram.conjugate BarringtonProgram.eval;
  induction' ( List.finRange BP.len ) using List.reverseRecOn with _ _ ih <;> aesop

/-
Define the negation of a Barrington program by appending a constant program that applies σ. Requires a variable index i to construct the constant program.
-/
def negate {n : ℕ} (BP : BarringtonProgram n) (i : Fin n) (σ : Equiv.Perm (Fin 5)) : BarringtonProgram n :=
  BP.append (BarringtonProgram.const i σ)

/-
The length of the negated program is the length of the original program plus 1.
-/
theorem len_negate {n : ℕ} (BP : BarringtonProgram n) (i : Fin n) (σ : Equiv.Perm (Fin 5)) :
    (BP.negate i σ).len = BP.len + 1 := by
  unfold negate
  rw [len_append]
  rfl

/-
Prove that the negation of a Barrington program computes the negation of the function.
-/
theorem computes_negate {n : ℕ} (BP : BarringtonProgram n) (i : Fin n) (f : (Fin n → Fin 2) → Fin 2) (σ : Equiv.Perm (Fin 5))
    (h : BP.computes f σ⁻¹) :
    (BP.negate i σ).computes (fun x ↦ 1 - f x) σ := by
  simp_all +decide [ computes ];
  intro x; have := h.2 x; simp_all +decide [ eval_append, negate ] ;
  cases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ <;> simp_all +decide [ eval_const ]

end BarringtonProgram

/-
Classify the gates in NC0_GateOps into AND, NOT, ID, and Const 1.
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

theorem NC0_gates_cases (op : GateOp (Fin 2)) (h : op ∈ NC_GateOps) :
    op.isAND ∨ op.isNOT ∨ op.isID ∨ op.isConst 1 := by
  revert h
  simp [NC_GateOps]
  rintro (rfl | rfl | rfl | rfl) <;> simp +decide [GateOp.isAND, GateOp.isNOT, GateOp.isID, GateOp.isConst];
  exact Fin.isEmpty'

/-
Define the recursive step for constructing a Barrington program from a circuit layer. We use `Classical` to allow branching on propositions.
-/
open Classical

noncomputable def BP_of_FeedForward_layer {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) : BarringtonProgram n :=
  let g := gates u
  if h_and : g.op.isAND then
    let e := Classical.choose h_and
    let v0 := g.inputs (e.symm 0)
    let v1 := g.inputs (e.symm 1)
    if h_cycle : σ.IsCycle ∧ σ.support.card = 5 then
      let x := Classical.choose (exists_commutator_eq_cycle σ h_cycle)
      let y := Classical.choose (Classical.choose_spec (exists_commutator_eq_cycle σ h_cycle))
      (prev_BPs v0 y⁻¹).commutator (prev_BPs v1 x⁻¹)
    else
      BarringtonProgram.const ⟨0, hn⟩ 1
  else if h_not : g.op.isNOT then
    let e := Classical.choose h_not
    let v := g.inputs (e.symm 0)
    (prev_BPs v σ⁻¹).negate ⟨0, hn⟩ σ
  else if h_id : g.op.isID then
    let e := Classical.choose h_id
    let v := g.inputs (e.symm 0)
    prev_BPs v σ
  else
    BarringtonProgram.const ⟨0, hn⟩ σ

/-
Define the full Barrington program construction by induction on the circuit depth.
-/
noncomputable def BP_of_FeedForward {n : ℕ} (hn : n > 0)
    (F : FeedForward (Fin 2) (Fin n) (Fin 1))
    (d : Fin (F.depth + 1)) :
    F.nodes d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n :=
  @Fin.induction _ (fun d => F.nodes d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (fun i σ =>
      BarringtonProgram.ofVar (cast F.nodes_zero i) σ)
    (fun d prev_BPs => BP_of_FeedForward_layer hn (F.gates d) prev_BPs)
    d

/-
Prove that the length of the constructed Barrington program layer is at most 4 times the maximum length of the previous layer programs.
-/
theorem BP_of_FeedForward_layer_len {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    {prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n}
    {L : ℕ} (hL : 1 ≤ L)
    (h_prev : ∀ v σ, (prev_BPs v σ).len ≤ L)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).len ≤ 4 * L := by
  unfold BP_of_FeedForward_layer;
  dsimp only [Fin.isValue]
  split_ifs <;> norm_num [ BarringtonProgram.len_commutator, BarringtonProgram.len_negate ];
  · grind;
  · exact Nat.one_le_iff_ne_zero.mpr ( by positivity );
  · linarith [ h_prev ( ( gates u ).inputs ( ( Classical.choose ‹ ( gates u |> Gate.op ) |> GateOp.isNOT › ).symm 0 ) ) σ⁻¹ ];
  · grind;
  · exact Nat.one_le_iff_ne_zero.mpr ( by positivity )

/-
Prove that the length of the constructed Barrington program is at most $4^d$.
-/
theorem BP_of_FeedForward_len {n : ℕ} (hn : n > 0)
    (F : FeedForward (Fin 2) (Fin n) (Fin 1))
    (d : Fin (F.depth + 1)) (u : F.nodes d) (σ : Equiv.Perm (Fin 5)) :
    (BP_of_FeedForward hn F d u σ).len ≤ 4 ^ (d : ℕ) := by
  -- We proceed by induction on the depth $d$.
  induction' d using Fin.induction with d ih generalizing σ;
  · exact Nat.le_of_ble_eq_true rfl;
  · simp only [Fin.val_succ, pow_succ']
    exact BP_of_FeedForward_layer_len hn (F.gates d) (Nat.one_le_pow' d 3) ih u σ

-------------

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
If the gate is a NOT gate, the constructed Barrington program computes the negation of the input.
-/
theorem BP_of_FeedForward_layer_computes_NOT {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_BPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_not : (gates u).op.isNOT) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).computes
      (fun x ↦ (gates u).eval (input_vals · x)) σ := by
  unfold BP_of_FeedForward_layer
  field_simp
  split_ifs with h
  · exact False.elim <| not_isAND_of_isNOT h_not h
  · convert BarringtonProgram.computes_negate _ _ _ _ _ using 1
    rotate_left
    exact input_vals ((gates u).inputs (h_not.choose.symm 0))
    · exact h_prev _ _ ⟨by simpa using hσ.1.inv, by simpa using hσ.2⟩
    · funext x
      exact h_not.choose_spec _

/-
If the gate is an ID gate, the constructed Barrington program computes the identity of the input.
-/
theorem BP_of_FeedForward_layer_computes_ID {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_BPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_id : (gates u).op.isID) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
    have h_not_and : ¬(gates u).op.isAND := by
      obtain ⟨ e, he ⟩ := h_id;
      rintro ⟨ e', he' ⟩;
      have := e.cardinal_eq; have := e'.cardinal_eq; aesop;
    unfold BP_of_FeedForward_layer;
    have h_not_not : ¬(gates u).op.isNOT := by
      intro h_not;
      obtain ⟨e, he⟩ := h_id
      obtain ⟨e', he'⟩ := h_not
      have h_eq : e.symm 0 = e'.symm 0 := by
        have := e.symm.surjective ( e'.symm 0 ) ; have := e'.symm.surjective ( e.symm 0 ) ; aesop;
      have := he fun _ => 0; have := he' fun _ => 0; simp_all +decide ;
    simp [h_not_and, h_not_not, h_id];
    convert h_prev _ _ hσ using 2;
    exact h_id.choose_spec _

/-
If the gate is a Const 1 gate, the constructed Barrington program computes the constant 1 function.
-/
theorem BP_of_FeedForward_layer_computes_Const {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_const : (gates u).op.isConst 1) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
  apply Classical.byContradiction
  intro h_not_const;
  -- Since the gate is not a constant 1, it must be either an AND or a NOT gate.
  by_cases h_and : (gates u).op.isAND ∨ (gates u).op.isNOT ∨ (gates u).op.isID;
  · obtain h | h | h := h_and <;> simp_all +decide [ FeedForward.GateOp.isAND, FeedForward.GateOp.isNOT, FeedForward.GateOp.isID, FeedForward.GateOp.isConst ];
    · exact h_const.1.elim ( Classical.choose h |> Equiv.symm |> Equiv.toEmbedding |> fun e => e 0 );
    · exact h_const.1.elim ( h.choose.symm 0 );
    · obtain ⟨ e, he ⟩ := h;
      exact h_const.1.elim ( e.symm 0 );
  · unfold BP_of_FeedForward_layer at h_not_const; simp_all +decide ;
    unfold BarringtonProgram.computes at h_not_const; simp_all +decide ;
    obtain ⟨ x, hx ⟩ := h_not_const ( by rintro rfl; simp_all +decide ) ; simp_all +decide [ BarringtonProgram.eval_const ] ;
    unfold Gate.eval at hx; simp_all +decide [ GateOp.isConst ] ;

/-
If `σ` is the commutator of `x` and `y`, and `BP1` computes `f` with `y⁻¹` and `BP2` computes `g` with `x⁻¹`, then the commutator of `BP1` and `BP2` computes `f * g` with `σ`.
-/
lemma commutator_computes_AND_of_cycle_decomp {n : ℕ} (BP1 BP2 : BarringtonProgram n)
    (f g : (Fin n → Fin 2) → Fin 2) (σ x y : Equiv.Perm (Fin 5))
    (hσ : σ ≠ 1)
    (h_decomp : σ = x * y * x⁻¹ * y⁻¹)
    (h1 : BP1.computes f y⁻¹)
    (h2 : BP2.computes g x⁻¹) :
    (BP1.commutator BP2).computes (fun z ↦ f z * g z) σ := by
  convert BarringtonProgram.computes_and BP1 BP2 f g ( y⁻¹ ) ( x⁻¹ ) h1 h2 _ using 1;
  aesop

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
If the gate is an AND gate, the constructed Barrington program computes the AND of the inputs.
-/
theorem BP_of_FeedForward_layer_computes_AND {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_BPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_and : (gates u).op.isAND) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
  have h_apply_def : ∀ {w : Equiv.Perm (Fin 5)}, w.IsCycle ∧ w.support.card = 5 → (BP_of_FeedForward_layer hn gates prev_BPs u w).computes (fun x => (gates u).eval (fun v => input_vals v x)) w := by
    intros w hw
    unfold BP_of_FeedForward_layer;
    simp_all +decide only;
    split_ifs ; simp_all +decide only [Gate_eval_of_isAND];
    · apply_rules [ commutator_computes_AND_of_cycle_decomp ];
      · aesop;
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
Simplification lemma for `BP_of_FeedForward_layer` in the AND case.
-/
lemma BP_of_FeedForward_layer_eq_commutator {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (h_and : (gates u).op.isAND)
    (h_cycle : σ.IsCycle ∧ σ.support.card = 5) :
    BP_of_FeedForward_layer hn gates prev_BPs u σ =
      let e := Classical.choose h_and
      let x := Classical.choose (exists_commutator_eq_cycle σ h_cycle)
      let y := Classical.choose (Classical.choose_spec (exists_commutator_eq_cycle σ h_cycle))
    (prev_BPs ((gates u).inputs (e.symm 0)) y⁻¹).commutator (prev_BPs ((gates u).inputs (e.symm 1)) x⁻¹) := by
  simp_all [BP_of_FeedForward_layer]

/-
The Barrington program constructed for a layer computes the correct value, assuming the previous layer's programs are correct.
-/
theorem BP_of_FeedForward_layer_computes {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (input_vals : nodes_d → (Fin n → Fin 2) → Fin 2)
    (h_prev : ∀ (v : nodes_d) (σ : Equiv.Perm (Fin 5)),
      σ.IsCycle ∧ σ.support.card = 5 →
      (prev_BPs v σ).computes (input_vals v) σ)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5)
    (h_gates : (gates u).op ∈ NC_GateOps) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).computes
      (fun x ↦ (gates u).eval (fun v ↦ input_vals v x)) σ := by
  rcases (NC0_gates_cases (gates u).op h_gates) with h | h | h | h
  · exact BP_of_FeedForward_layer_computes_AND hn gates prev_BPs input_vals h_prev u σ hσ h
  · exact BP_of_FeedForward_layer_computes_NOT hn gates prev_BPs input_vals h_prev u σ hσ h
  · exact BP_of_FeedForward_layer_computes_ID hn gates prev_BPs input_vals h_prev u σ hσ h
  · exact BP_of_FeedForward_layer_computes_Const hn gates prev_BPs input_vals u σ hσ h

/-
The Barrington program constructed from a FeedForward circuit computes the same function as the circuit node.
-/
theorem BP_of_FeedForward_computes {n : ℕ} (hn : n > 0)
    (F : FeedForward (Fin 2) (Fin n) (Fin 1))
    (h_gates : F.onlyUsesGates NC_GateOps)
    (d : Fin (F.depth + 1)) (u : F.nodes d) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsCycle ∧ σ.support.card = 5) :
    (BP_of_FeedForward hn F d u σ).computes (fun x ↦ F.evalNode u x) σ := by
      -- Apply the induction hypothesis to the previous layer's programs.
      have h_ind : ∀ (v : F.nodes d) (σ : Equiv.Perm (Fin 5)), σ.IsCycle ∧ σ.support.card = 5 → (BP_of_FeedForward hn F d v σ).computes (fun x => F.evalNode v x) σ := by
        induction' d using Fin.induction with d ih;
        · unfold BarringtonProgram.computes; aesop;
        · intro v σ hσ
          have h_layer : (BP_of_FeedForward_layer hn (F.gates d) (BP_of_FeedForward hn F d.castSucc) v σ).computes (fun x => (F.gates d v).eval (fun n => F.evalNode n x)) σ := by
            apply BP_of_FeedForward_layer_computes;
            · exact fun v σ hσ => ih v v σ hσ;
            · exact hσ;
            · exact h_gates d v;
          convert h_layer using 1;
      exact h_ind u σ hσ

/-
The permutation (0 1 2 3 4) is a 5-cycle.
-/
def sigma_five_cycle : Equiv.Perm (Fin 5) :=
  finRotate 5

lemma sigma_five_cycle_is_cycle : sigma_five_cycle.IsCycle ∧ sigma_five_cycle.support.card = 5 := by
  simp +decide [Equiv.Perm.IsCycle]

/-
The length of the constructed Barrington program for a layer is at most 4 times the maximum length of the previous layer's programs.
-/
theorem BP_of_FeedForward_layer_len' {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (L : ℕ) (hL : 1 ≤ L)
    (h_prev : ∀ v σ, (prev_BPs v σ).len ≤ L)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).len ≤ 4 * L :=
  BP_of_FeedForward_layer_len hn gates hL h_prev u σ

/-
The length of the constructed Barrington program for a layer is at most 4 times the maximum length of the previous layer's programs.
-/
theorem BP_of_FeedForward_layer_len_aux {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram n)
    (L : ℕ) (hL : 1 ≤ L)
    (h_prev : ∀ v σ, (prev_BPs v σ).len ≤ L)
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) :
    (BP_of_FeedForward_layer hn gates prev_BPs u σ).len ≤ 4 * L :=
  BP_of_FeedForward_layer_len hn gates hL h_prev u σ

/-
The length of the constructed Barrington program is at most 4^d.
-/
theorem BP_of_FeedForward_len_aux {n : ℕ} (hn : n > 0)
    (F : FeedForward (Fin 2) (Fin n) (Fin 1))
    (d : Fin (F.depth + 1)) (u : F.nodes d) (σ : Equiv.Perm (Fin 5)) :
    (BP_of_FeedForward hn F d u σ).len ≤ 4 ^ (d : ℕ) := by
  have := @BP_of_FeedForward_len; aesop;

/-
Convert a CircuitFamily to a BPFamily using Barrington's construction for n > 0. For n=0, return a trivial BP. For depth 0 circuits (n=1), return a variable BP.
-/
noncomputable def BP_of_CircuitFamily {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out) : BPFamily (Fin 2) :=
  fun n ↦
    if hn : n = 0 then
      -- Trivial BP for n=0. Just evaluate and return that.
      { depth := 0
        nodes := fun _ ↦ Fin 1
        nodeVar := fun {k} _ ↦ k.elim0
        edges := fun {k} _ ↦ k.elim0
        startUnique := { default := 0, uniq := fun _ ↦ Fin.eq_zero _ }
        retVals := fun _ ↦ (CF 0).eval₁ (fun x ↦ x.elim0)
      }
    else
      let F := CF n
      if h_depth : F.depth = 0 then
        -- Depth 0 case (implies n=1)
        (BarringtonProgram.ofVar ⟨0, Nat.pos_of_ne_zero hn⟩ sigma_five_cycle).toBP sigma_five_cycle
      else
        -- Depth > 0 case
        let F' := F.relabelOut h_depth (Equiv.ofUnique out (Fin 1))
        let d := Fin.last F'.depth
        let u : F'.nodes d := cast F'.nodes_last.symm 0
        let BP := BP_of_FeedForward (Nat.pos_of_ne_zero hn) F' d u sigma_five_cycle
        BP.toBP sigma_five_cycle

/-
The permutation (0 1 2 3 4) does not map 0 to 0.
-/
lemma sigma_five_cycle_zero_ne_zero : sigma_five_cycle 0 ≠ 0 := by
  decide

/-
The permutation (0 1 2 3 4) is not the identity.
-/
lemma sigma_five_cycle_ne_one : sigma_five_cycle ≠ 1 := by
  decide

/-
Partial evaluation of a Barrington program using the first k instructions.
-/
def BarringtonProgram.eval_partial {n : ℕ} (BP : BarringtonProgram n) (k : ℕ) (x : Fin n → Fin 2) : Equiv.Perm (Fin 5) :=
  ((List.finRange BP.len).take k).foldl (fun acc i ↦
    let p := if x (BP.var i) = 1 then BP.perm1 i else BP.perm0 i
    p * acc) 1

/-
Evaluation is equivalent to partial evaluation at the full length.
-/
theorem BarringtonProgram.eval_eq_eval_partial {n : ℕ} (BP : BarringtonProgram n) (x : Fin n → Fin 2) :
    BP.eval x = BP.eval_partial BP.len x := by
  rw [eval_partial, List.take_of_length_le (by simp)]
  exact rfl

/-
The nodes at layer k > 0 in the converted branching program are Fin 5.
-/
lemma BarringtonProgram.toBP_nodes_eq_fin5 {n : ℕ} (BP : BarringtonProgram n) (σ : Equiv.Perm (Fin 5)) (k : ℕ) (hk : k ≤ BP.len) (hk0 : 0 < k) :
    (BP.toBP σ).nodes ⟨k, Nat.lt_succ_of_le hk⟩ = Fin 5 := by
  cases k <;> aesop

/-
The node reached at layer k in the converted branching program corresponds to the value of 0 under the partial evaluation of the Barrington program.
-/
theorem BarringtonProgram.toBP_evalLayer_eq_eval_partial {n : ℕ} (BP : BarringtonProgram n) (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) (k : ℕ) (hk : k ≤ BP.len) (hk0 : 0 < k) :
    cast (toBP_nodes_eq_fin5 BP σ k hk hk0) ((BP.toBP σ).evalLayer ⟨k, Nat.lt_succ_of_le hk⟩ x) = (BP.eval_partial k x) 0 := by
  generalize_proofs at *;
  induction' k with k ih <;> simp_all [ Nat.succ_eq_add_one ];
  cases k <;> simp_all [ Nat.succ_eq_add_one]
  · unfold eval_partial;
    rcases BP with ⟨ _ | _, _, _, _ ⟩ <;> norm_num [ List.finRange ] at *;
    unfold toBP; aesop;
  · rename_i k hk₁ hk₂;
    convert congr_arg ( fun u => ( if x ( BP.var ⟨ k + 1, by linarith ⟩ ) = 1 then BP.perm1 ⟨ k + 1, by linarith ⟩ else BP.perm0 ⟨ k + 1, by linarith ⟩ ) u ) ( ih ( by linarith ) ( by exact Nat.lt_of_succ_lt ( by linarith ) ) ( by
      exact hk₂ ) ) using 1
    generalize_proofs at *;
    unfold eval_partial
    simp [List.take_succ]
    split_ifs <;> simp_all

/-
The evaluation of the converted branching program is correct (assuming length > 0).
-/
theorem BarringtonProgram.toBP_eval {n : ℕ} (BP : BarringtonProgram n) (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) (h_len : BP.len > 0) :
    (BP.toBP σ).eval x = if (BP.eval x) 0 = σ 0 then 1 else 0 := by
  -- Since BP.len > 0, the last layer is at index BP.len. By definition of toBP, the nodes at this layer are Fin 5.
  have h_last_layer : (BP.toBP σ).nodes ⟨BP.len, Nat.lt_succ_self _⟩ = Fin 5 := by
    exact if_neg ( by aesop );
  -- By definition of toBP, the evaluation at the last layer is the result of applying the permutation σ to the value at 0.
  have h_eval_last_layer : (BP.toBP σ).eval x = if (cast h_last_layer ((BP.toBP σ).evalLayer ⟨BP.len, Nat.lt_succ_self _⟩ x)) = σ 0 then 1 else 0 := by
    have h_depth : (BP.toBP σ).depth = BP.len := by
      rfl
    unfold toBP at * ; aesop;
  convert h_eval_last_layer using 2;
  rw [toBP_evalLayer_eq_eval_partial]
  · rw [eval_eq_eval_partial]
  · norm_num
  · linarith

/-
The branching program family constructed from a circuit family has width at most 5.
-/
theorem BarringtonProgram.of_CircuitFamily_hasWidth_five {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out) :
    (BP_of_CircuitFamily CF).hasWidth (·≤5) := by
  intro n
  dsimp [BP_of_CircuitFamily]
  split_ifs with hn
  · simp [LayeredBranchingProgram.width]
  · apply width_toBP
  · apply width_toBP

/-
If a circuit family has logarithmic depth, the constructed branching program family has polynomial depth.
-/
theorem BarringtonProgram.of_CircuitFamily_hasDepth_poly {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out)
    (h_depth : CF.hasDepth GrowthRate.log) :
    (BP_of_CircuitFamily CF).hasDepth GrowthRate.poly := by
  apply GrowthRate.mono (f := fun n ↦ 4 ^ (CF n).depth)
  · refine GrowthRate.exp_comp_log ?_ h_depth
    exact ⟨4, by simpa using Asymptotics.isBigO_refl ..⟩
  · intro n
    dsimp [BP_of_CircuitFamily]
    split_ifs
    · simp [*]
    · simp [*]
      rfl
    · refine (BP_of_FeedForward_len ..).trans ?_
      simp [FeedForward.relabelOut]

/-
For any layer except the last one, the nodes of the relabeled circuit are the same as the original circuit.
-/
theorem FeedForward.nodes_relabelOut_eq {α inp out a} (F : FeedForward α inp out)
    (hF : F.depth ≠ 0) (e : out ≃ a) (d : Fin (F.depth + 1)) (hd : d < Fin.last F.depth) :
    (F.relabelOut hF e).nodes d = F.nodes d := by
  unfold relabelOut
  rw [ite_eq_right_iff]
  rintro rfl
  simp at hd

/-
For any layer except the last one, the gates of the relabeled circuit are heterogeneously equal to the original circuit.
-/
theorem FeedForward.gates_relabelOut_heq {α inp out a} (F : FeedForward α inp out)
    (hF : F.depth ≠ 0) (e : out ≃ a) (k : Fin F.depth) (hk : k.val < F.depth - 1)
    (n : (F.relabelOut hF e).nodes k.succ) :
    HEq ((F.relabelOut hF e).gates k n) (F.gates k (cast (by
        rw [FeedForward.nodes_relabelOut_eq F hF e k.succ (by
          simp [Fin.lt_iff_val_lt_val]
          omega
        )]
      ) n)) := by
  generalize_proofs at *;
  unfold FeedForward.relabelOut; aesop;

/-
For any layer except the last one, the evaluation of a node in the relabeled circuit is the same as in the original circuit.
-/
theorem FeedForward.evalNode_relabelOut_lt {α inp out a} (F : FeedForward α inp out)
    (hF : F.depth ≠ 0) (e : out ≃ a) (d : Fin (F.depth + 1)) (hd : d < Fin.last F.depth)
    (node : (F.relabelOut hF e).nodes d) (x : inp → α) :
    (F.relabelOut hF e).evalNode node x =
      F.evalNode (cast (FeedForward.nodes_relabelOut_eq F hF e d hd) node) x := by
  have h_nodes_eq : ∀ k : Fin (F.depth + 1), k < Fin.last F.depth → (F.relabelOut hF e).nodes k = F.nodes k := by
    exact fun k a_1 ↦ nodes_relabelOut_eq F hF e k a_1
  generalize_proofs at *;
  induction' d using Fin.inductionOn with i IH;
  · cases F ; aesop;
  · simp_all [ Fin.lt_iff_val_lt_val ];
    have h_gates_eq : ∀ (node : (F.relabelOut hF e).nodes (Fin.succ i)), HEq ((F.relabelOut hF e).gates i node) (F.gates i (cast ‹_› node)) := by
      apply FeedForward.gates_relabelOut_heq;
      exact Nat.lt_pred_iff.mpr hd;
    -- Apply the equality of gates to the evaluation.
    change ((F.relabelOut hF e).gates i node).eval (fun v => (F.relabelOut hF e).evalNode v x) = (F.gates i (cast ‹_› node)).eval (fun v => F.evalNode v x)
    rw [ FeedForward.Gate.eval, FeedForward.Gate.eval ];
    congr! 1 with e_2
    · grind;
    · congr! 1
      · exact congrArg GateOp.ι e_2
      · grind

/-
For any layer except the last one, the gates of the relabeled circuit are equal (modulo casts) to the original circuit.
-/
theorem FeedForward.gates_relabelOut_eq {α inp out a} (F : FeedForward α inp out)
    (hF : F.depth ≠ 0) (e : out ≃ a) (k : Fin F.depth) (hk : k.val < F.depth - 1)
    (n : (F.relabelOut hF e).nodes k.succ) :
    (F.relabelOut hF e).gates k n =
      cast (by rw [nodes_relabelOut_eq F hF e k.castSucc k.castSucc_lt_last])
      (F.gates k (cast (nodes_relabelOut_eq F hF e k.succ (Nat.lt_pred_iff.mp hk)) n)) := by
  have := gates_relabelOut_heq F hF e k hk n
  grind

/-
Evaluating a casted gate is equivalent to evaluating the original gate with casted inputs.
-/
lemma FeedForward.Gate.eval_cast {α : Type u} {domain domain' : Type v}
    (g : FeedForward.Gate α domain) (h : domain = domain') (xs : domain' → α) :
    (cast (congrArg (FeedForward.Gate α) h) g).eval xs = g.eval (fun d ↦ xs (cast h d)) := by
  subst h
  rfl

/-
The size of a branching program in a family with bounded width is bounded by width * depth + 1.
-/
theorem BPFamily.size_le_bound (BPF : BPFamily α) [BPF.Finite] (w : ℕ) (hw : BPF.hasWidth (·≤w)) :
    ∀ n, (BPF n).size ≤ w * (BPF n).depth + 1 := by
  -- Apply the lemma that relates the size of a layer to its width and depth, and use the fact that the width is bounded by w.
  intros n
  have h_width : (BPF n).width ≤ w := by
    exact hw n
  have h_size : (BPF n).size ≤ (BPF n).width * (BPF n).depth + 1 := by
    convert LayeredBranchingProgram.size_le_width_mul_depth _;
    -- Since BPF is a family of finite branching programs, each BPF n is finite by definition.
    apply (‹BPFamily.Finite BPF›).finite
  exact h_size.trans (by
  exact Nat.succ_le_succ ( Nat.mul_le_mul_right _ h_width ))

theorem GrowthRate.const_mem_const (k : ℕ) : (fun _ ↦ k) ∈ GrowthRate.const := by
  simp [const, bigO]
  use k
  simp

lemma GrowthRate.affine_comp {S : GrowthRate} [LawfulGrowthRate S] {f : ℕ → ℕ} {a b : ℕ} (hf : f ∈ S) :
    (fun n ↦ a * f n + b) ∈ S :=
  GrowthRate.add
    (GrowthRate.const_mul (GrowthRate.const_mem_const a) hf)
    (GrowthRate.const_mem <| GrowthRate.const_mem_const b)

/-
If a branching program family has constant width and polynomial depth, it has polynomial size.
-/
theorem BPFamily.hasSize_poly_of_hasWidth_const_hasDepth_poly (BPF : BPFamily α) [BPF.Finite]
    (w : ℕ) (hw : BPF.hasWidth (·≤w)) (hd : BPF.hasDepth GrowthRate.poly) :
    BPF.hasSize GrowthRate.poly := by
  -- Let `f(n) = (BPF n).depth`. We are given `f ∈ GrowthRate.poly` (by `hd`).
  set f : ℕ → ℕ := fun n => (BPF n).depth
  have hf : f ∈ GrowthRate.poly := hd;
  -- Let `g(n) = w * f(n) + 1`. By `GrowthRate.poly_affine_closure'`, `g ∈ GrowthRate.poly`.
  set g : ℕ → ℕ := fun n => w * f n + 1
  have hg : g ∈ GrowthRate.poly := GrowthRate.affine_comp hf
  -- Since `GrowthRate.poly` is a `LawfulGrowthRate`, we can use `LawfulGrowthRate.mem_dominating`.
  have h_dominating : ∀ᶠ n in Filter.atTop, (BPF n).size ≤ g n := by
    have := @BPFamily.size_le_bound _ BPF ‹_› w hw; aesop;
  -- Apply the `LawfulGrowthRate.mem_dominating` lemma with `g` and `h`, since `g ∈ GrowthRate.poly` and `h` is dominated by `g`, we conclude `h ∈ GrowthRate.poly`.
  have h_final : (fun n => (BPF n).size) ∈ GrowthRate.poly := by
    have h_mem : (fun n => (BPF n).size) ≤ᶠ[Filter.atTop] g := h_dominating
    exact GrowthRate.mem_dominating h_dominating hg;
  exact h_final

/-
If a Barrington program computes a function f with permutation sigma, then its converted branching program computes f.
-/
theorem BarringtonProgram.toBP_computes_of_computes {n : ℕ} (BP : BarringtonProgram n)
    (f : (Fin n → Fin 2) → Fin 2) (σ : Equiv.Perm (Fin 5))
    (hσ0 : σ 0 ≠ 0) (hlen : BP.len > 0) (h : BP.computes f σ) :
    (BP.toBP σ).computes f := by
  rw [LayeredBranchingProgram.computes]
  intro x
  rw [BarringtonProgram.toBP_eval BP σ x hlen]
  have h_eval : BP.eval x = if f x = 1 then σ else 1 := h.2 x
  rcases Fin.exists_fin_two.mp ⟨f x, rfl⟩ with h | h
  · simp [h_eval, h, hσ0.symm]
  · simp [h_eval, h]
