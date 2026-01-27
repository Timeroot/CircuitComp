
import CircuitComp.NC
import CircuitComp.BranchingProgram.Basic

import Mathlib.GroupTheory.SpecificGroups.Alternating

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}

open LayeredBranchingProgram

/-
Define BarringtonProgram and its evaluation. The type `g` is typically a group (but in general
just needs some multiplicative structure). The types `perm0` and `perm1` are used depending on
the value of each variable, indexed by the types `α`.
-/
structure BarringtonProgram (α : Type u) (G : Type v) where
  len : ℕ
  var : Fin len → α
  perm0 : Fin len → G
  perm1 : Fin len → G

namespace BarringtonProgram

variable {α : Type u} {G : Type v} (BP BP1 BP2 : BarringtonProgram α G)

def eval [Mul G] [One G] (x : α → Fin 2) : G :=
  (List.finRange BP.len).foldl (fun acc i ↦
    let p := if x (BP.var i) = 1 then BP.perm1 i else BP.perm0 i
    p * acc) (1 : G)

def computes [Mul G] [One G] (f : (α → Fin 2) → Fin 2) (σ : G) : Prop :=
  σ ≠ 1 ∧ ∀ x, BP.eval x = if f x = 1 then σ else 1

/--
The concatenation of two Barrington programs and prove that the evaluation of the
concatenated program is the product of the evaluations (note the order due to function
composition/multiplication convention).
-/
def append : BarringtonProgram α G where
  len := BP1.len + BP2.len
  var := Fin.append BP1.var BP2.var
  perm0 := Fin.append BP1.perm0 BP2.perm0
  perm1 := Fin.append BP1.perm1 BP2.perm1

theorem len_append : (append BP1 BP2).len = BP1.len + BP2.len :=
  rfl

theorem eval_append [Monoid G] (BP1 BP2 : BarringtonProgram α G) (x : α → Fin 2) :
    (BP1.append BP2).eval x = BP2.eval x * BP1.eval x := by
  unfold append eval;
  rw [ show List.finRange (BP1.len + BP2.len) = List.map (Fin.castAdd BP2.len) (List.finRange BP1.len) ++ List.map ( fun i => Fin.natAdd BP1.len i ) ( List.finRange BP2.len ) from ?_, List.foldl_append ];
  · simp [Fin.append, List.foldl_map]
    induction (List.finRange BP2.len) using List.reverseRecOn
    · simp
    · simp_all [mul_assoc]
  · apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      by_cases hi₃ : i < BP1.len
      · simp [hi₃]
      · simp_all
/-
Define the reverse of a Barrington program and prove that its evaluation is the inverse of the original program's evaluation.
-/
def reverse [Inv G] : BarringtonProgram α G where
  len := BP.len
  var := BP.var ∘ Fin.rev
  perm0 := fun i ↦ (BP.perm0 (Fin.rev i))⁻¹
  perm1 := fun i ↦ (BP.perm1 (Fin.rev i))⁻¹

theorem eval_reverse [Group G] (x : α → Fin 2) :
    BP.reverse.eval x = (BP.eval x)⁻¹ := by
  unfold eval reverse
  -- By definition of `List.finRange`, we can rewrite the left-hand side to match the right-hand side.
  have h_finRange : List.finRange BP.len = List.map (fun i => Fin.rev i) (List.finRange BP.len).reverse := by
    refine' List.ext_get _ _ <;> simp [ Fin.rev ];
    exact fun i hi => by omega;
  conv_rhs => rw [ h_finRange ];
  induction' ( List.finRange BP.len ) using List.reverseRecOn with i _ ih <;> simp [ * ];
  split_ifs <;> simp_all +singlePass [ List.foldr_map];
  · induction i
    · simp
    simp only [Fin.isValue, List.foldr_cons]
    split_ifs <;> simp [*, ← mul_assoc]
  · induction i
    · simp
    simp only [Fin.isValue, List.foldr_cons]
    split_ifs <;> simp [*, ← mul_assoc]

/-
Define a Barrington program for a single variable and prove it computes the variable.
-/
def ofVar (i : α) [One G] (σ : G) : BarringtonProgram α G where
  len := 1
  var := fun _ ↦ i
  perm0 := fun _ ↦ 1
  perm1 := fun _ ↦ σ

theorem eval_ofVar [MulOneClass G] (i : α) (σ : G) (x : α → Fin 2) :
    (BarringtonProgram.ofVar i σ).eval x = if x i = 1 then σ else 1 := by
  simp [ofVar, eval, List.finRange_succ]

/-
Define a constant Barrington program (reading a dummy variable) and prove it evaluates to the constant permutation.
-/
def const (i : α) (σ : G) : BarringtonProgram α G where
  len := 1
  var := fun _ ↦ i
  perm0 := fun _ ↦ σ
  perm1 := fun _ ↦ σ

theorem eval_const [MulOneClass G] (i : α) (σ : G) (x : α → Fin 2) :
    (BarringtonProgram.const i σ).eval x = σ := by
  simp [eval, const, Fin.isValue, ite_self, List.finRange_succ]

/-
Define the commutator of two Barrington programs and prove its length is twice the sum of the lengths of the original programs.
-/
def commutator [Group G] : BarringtonProgram α G :=
  (BP1.append BP2).append (BP1.reverse.append BP2.reverse)

theorem len_commutator [Group G] :
    (BP1.commutator BP2).len = 2 * BP1.len + 2 * BP2.len := by
  simp +arith [commutator, len_append, reverse]

/-
Prove that the evaluation of the commutator program is the commutator of the evaluations.
-/
theorem eval_commutator [Group G] (x : α → Fin 2) :
    (BP1.commutator BP2).eval x = (BP2.eval x)⁻¹ * (BP1.eval x)⁻¹ * BP2.eval x * BP1.eval x := by
  unfold commutator;
  rw [eval_append, eval_append, eval_append, eval_reverse, eval_reverse]
  group


/--
Define the conversion from a Barrington Program to a Layered Branching Program.
-/
def toBP (BP : BarringtonProgram α G) (σ : G) (γ : Type) [Zero γ] [DecidableEq γ] [SMul G γ] :
    LayeredBranchingProgram α (Fin 2) (Fin 2) where
  depth := BP.len
  nodes := fun i ↦ if i.val = 0 then Fin 1 else γ
  nodeVar := fun {k} _ ↦ BP.var k
  edges := fun {k} u b ↦
    if hk : k.val = 0 then
      let p := if b = 1 then BP.perm1 k else BP.perm0 k
      let dest : γ := p • 0
      dest
    else
      let u' : γ := cast (by simp [hk]) u
      let p := if b = 1 then BP.perm1 k else BP.perm0 k
      p • u'
  startUnique := {
    default := cast (by simp) (0 : Fin 1)
    uniq := fun x ↦ Fin.eq_zero _
  }
  retVals := fun u ↦
    if h : BP.len = 0 then
      0
    else
      let u' : γ := cast (by simp [h]) u
      if u' = σ • 0 then 1 else 0

/-
The width of the converted branching program is at most 5.
-/
theorem width_toBP (BP : BarringtonProgram α G) (σ : G)
    (γ : Type) [Zero γ] [DecidableEq γ] [SMul G γ] [Fintype γ] :
    (BP.toBP σ γ).width ≤ Fintype.card γ := by
  apply ciSup_le
  unfold toBP
  intro x
  simp only [Nat.succ_eq_add_one, Fin.val_eq_zero_iff]
  split
  · subst x
    simp
    apply Fintype.card_pos
  · simp


/-
Prove that any 5-cycle in $S_5$ can be written as a commutator of two 5-cycles.
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
theorem computes_ofVar {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin 5)) (hσ : σ ≠ 1) :
    (BarringtonProgram.ofVar i σ).computes (fun x ↦ x i) σ := by
  unfold computes; aesop

/-
Prove that the commutator of two Barrington programs computes the AND of their functions, given that the resulting commutator permutation is non-identity.
-/
theorem computes_and [Group G] (BP1 BP2 : BarringtonProgram α G)
    (f g : (α → Fin 2) → Fin 2) (a b : G)
    (h1 : BP1.computes f a) (h2 : BP2.computes g b)
    (h_comm : b⁻¹ * a⁻¹ * b * a ≠ 1) :
    (BP1.commutator BP2).computes (fun x ↦ f x * g x) (b⁻¹ * a⁻¹ * b * a) := by
  unfold computes at *
  refine ⟨h_comm, fun x ↦ ?_⟩
  simp [ *, BarringtonProgram.eval_commutator ]
  split_ifs <;> simp_all [ mul_assoc ]
  grind

/-
Define the conjugate of a Barrington program and prove its evaluation property.
-/
def conjugate [Group G] (BP : BarringtonProgram α G) (ρ : G) : BarringtonProgram α G where
  len := BP.len
  var := BP.var
  perm0 := fun i ↦ ρ * BP.perm0 i * ρ⁻¹
  perm1 := fun i ↦ ρ * BP.perm1 i * ρ⁻¹

theorem eval_conjugate [Group G] (BP : BarringtonProgram α G) (ρ : G) (x : α → Fin 2) :
    (BP.conjugate ρ).eval x = ρ * BP.eval x * ρ⁻¹ := by
  unfold BarringtonProgram.conjugate BarringtonProgram.eval;
  induction' ( List.finRange BP.len ) using List.reverseRecOn with _ _ ih <;> aesop

/-
Define the negation of a Barrington program by appending a constant program that applies σ. Requires a variable index i to construct the constant program.
-/
def negate [Group G] (BP : BarringtonProgram α G) (i : α) (σ : G) : BarringtonProgram α G :=
  BP.append (BarringtonProgram.const i σ)

/-
The length of the negated program is the length of the original program plus 1.
-/
theorem len_negate [Group G] (BP : BarringtonProgram α G) (i : α) (σ : G) :
    (BP.negate i σ).len = BP.len + 1 := by
  unfold negate
  rw [len_append]
  rfl

/-
Prove that the negation of a Barrington program computes the negation of the function.
-/
theorem computes_negate [Group G] (BP : BarringtonProgram α G) (i : α) (f : (α → Fin 2) → Fin 2) (σ : G)
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
    (u : nodes_succ) (σ : Equiv.Perm (Fin 5)) : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)) :=
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
    {out : Type} [Unique out] (F : FeedForward (Fin 2) (Fin n) out)
    (d : Fin (F.depth + 1)) :
    F.nodes d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)) :=
  @Fin.induction _ (fun d => F.nodes d →
      (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
    (fun i σ =>
      BarringtonProgram.ofVar (cast F.nodes_zero i) σ)
    (fun d prev_BPs => BP_of_FeedForward_layer hn (F.gates d) prev_BPs)
    d

/-
Prove that the length of the constructed Barrington program layer is at most 4 times the maximum length of the previous layer programs.
-/
theorem BP_of_FeedForward_layer_len {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    {prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5))}
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
theorem BP_of_FeedForward_len {out : Type} [Unique out] {n : ℕ} (hn : n > 0)
    (F : FeedForward (Fin 2) (Fin n) out)
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
lemma commutator_computes_AND_of_cycle_decomp {n : ℕ} (BP1 BP2 : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    {out : Type} [Unique out] {F : FeedForward (Fin 2) (Fin n) out}
    (h_gates : F.onlyUsesGates NC_GateOps)
    {d : Fin (F.depth + 1)} (u : F.nodes d) {σ : Equiv.Perm (Fin 5)}
    (hσ : σ.IsCycle ∧ σ.support.card = 5) :
    (BP_of_FeedForward hn F d u σ).computes (F.evalNode u) σ := by
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
The length of the constructed Barrington program for a layer is at most 4 times the maximum length of the previous layer's programs.
-/
theorem BP_of_FeedForward_layer_len' {n : ℕ} (hn : n > 0) {nodes_d nodes_succ : Type}
    (gates : nodes_succ → FeedForward.Gate (Fin 2) nodes_d)
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
    (prev_BPs : nodes_d → (σ : Equiv.Perm (Fin 5)) → BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
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
      let u : F.nodes (Fin.last F.depth) := cast F.nodes_last.symm (default : out)
      let BP := BP_of_FeedForward (Nat.pos_of_ne_zero hn) F _ u sigma_five_cycle
      (BP).toBP sigma_five_cycle (Fin 5)

/-
Partial evaluation of a Barrington program using the first k instructions.
-/
def BarringtonProgram.eval_partial {n : ℕ} (BP : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5))) (k : ℕ) (x : Fin n → Fin 2) : Equiv.Perm (Fin 5) :=
  ((List.finRange BP.len).take k).foldl (fun acc i ↦
    let p := if x (BP.var i) = 1 then BP.perm1 i else BP.perm0 i
    p * acc) 1

/-
Evaluation is equivalent to partial evaluation at the full length.
-/
theorem BarringtonProgram.eval_eq_eval_partial {n : ℕ} (BP : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5))) (x : Fin n → Fin 2) :
    BP.eval x = BP.eval_partial BP.len x := by
  rw [eval_partial, List.take_of_length_le (by simp)]
  rfl

/-
The nodes at layer k > 0 in the converted branching program are Fin 5.
-/
lemma BarringtonProgram.toBP_nodes_eq_fin5 {n : ℕ} (BP : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5))) (σ : Equiv.Perm (Fin 5)) (k : ℕ) (hk : k ≤ BP.len) (hk0 : 0 < k) :
    (BP.toBP σ (Fin 5)).nodes ⟨k, Nat.lt_succ_of_le hk⟩ = Fin 5 := by
  cases k <;> aesop

/-
The node reached at layer k in the converted branching program corresponds to the value of 0 under the partial evaluation of the Barrington program.
-/
theorem BarringtonProgram.toBP_evalLayer_eq_eval_partial {n : ℕ} (BP : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5))) (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) (k : ℕ) (hk : k ≤ BP.len) (hk0 : 0 < k) :
    cast (toBP_nodes_eq_fin5 BP σ k hk hk0) ((BP.toBP σ (Fin 5)).evalLayer ⟨k, Nat.lt_succ_of_le hk⟩ x) = (BP.eval_partial k x) 0 := by
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
theorem BarringtonProgram.toBP_eval {n : ℕ} (BP : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
    (σ : Equiv.Perm (Fin 5)) (x : Fin n → Fin 2) (hσ : σ 0 ≠ 0):
    (BP.toBP σ (Fin 5)).eval x = if (BP.eval x) 0 = σ 0 then 1 else 0 := by
  by_cases h_len : BP.len = 0
  · rcases BP with ⟨len, var, perm0, perm1⟩
    dsimp at h_len
    subst len
    simp [eval, toBP, LayeredBranchingProgram.eval ]
    exact hσ.symm
  replace h_len : 0 < BP.len := by omega
  -- Since BP.len > 0, the last layer is at index BP.len. By definition of toBP, the nodes at this layer are Fin 5.
  have h_last_layer : (BP.toBP σ (Fin 5)).nodes ⟨BP.len, Nat.lt_succ_self _⟩ = Fin 5 :=
    if_neg h_len.ne'
  -- By definition of toBP, the evaluation at the last layer is the result of applying the permutation σ to the value at 0.
  have h_eval_last_layer : (BP.toBP σ (Fin 5)).eval x = if (cast h_last_layer ((BP.toBP σ (Fin 5)).evalLayer ⟨BP.len, Nat.lt_succ_self _⟩ x)) = σ 0 then 1 else 0 := by
    unfold toBP at *
    simp only [Nat.succ_eq_add_one, Fin.val_eq_zero_iff, Fin.coe_castSucc, Fin.isValue, ite_smul,
      Equiv.Perm.smul_def, Fin.val_succ, Nat.add_eq_zero, one_ne_zero, and_false, ↓dreduceIte, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, cast_eq, Fin.val_last, Lean.Elab.WF.paramLet]
    split
    · simp_all only [lt_self_iff_false]
    · dsimp at h_last_layer
      sorry
  convert h_eval_last_layer using 2;
  rw [toBP_evalLayer_eq_eval_partial]
  · rw [eval_eq_eval_partial]
  · norm_num
  · linarith

theorem BarringtonProgram.of_CircuitFamily_IsOblivious {out : Type} [Unique out]
    (CF : CircuitFamily₁ (Fin 2) out) :
    (BP_of_CircuitFamily CF).IsOblivious := by
  intro n
  dsimp [BP_of_CircuitFamily]
  split_ifs with hn
  <;> simp [toBP, LayeredBranchingProgram.IsOblivious]
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
    · dsimp [toBP] --make this step a lemma: f.toBP.depth = f.len
      grw [BP_of_FeedForward_len]
      simp

theorem BarringtonProgram.of_CircuitFamily_computes {out : Type} [Unique out]
    {CF : CircuitFamily₁ (Fin 2) out} {f : FuncFamily₁ (Fin 2)}
    (hcf : CF.computes₁ f) (hcf_gates : CF.onlyUsesGates NC_GateOps):
    (BP_of_CircuitFamily CF).computes f := by
  intro n
  rw [BP_of_CircuitFamily]
  rcases n with _ | n
  · simp only [reduceDIte]
    unfold LayeredBranchingProgram.eval
    convert hcf 0
  rw [← hcf (n + 1)]
  simp
  generalize_proofs pf1 pf2
  have h := BP_of_FeedForward_computes pf1 (hcf_gates (n + 1)) (cast pf2 default) sigma_five_cycle_is_cycle
  unfold computes at h
  rcases h with ⟨h, h'⟩
  ext1 x
  rw [BarringtonProgram.toBP_eval _ _ _ (by decide), h' x]
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

instance BP_of_CircuitFamily_Finite {out : Type} [Unique out]
  (CF : CircuitFamily₁ (Fin 2) out) [CF.Finite] :
    (BP_of_CircuitFamily CF).Finite := by
  constructor
  intro n
  dsimp [BP_of_CircuitFamily]
  split_ifs with hn
  · constructor
    intro i
    simp
    infer_instance
  · constructor
    intro i
    sorry

/-
The size of a branching program in a family with bounded width is bounded by width * depth + 1.
-/
theorem BPFamily.size_le_bound (BPF : BPFamily α) [BPF.Finite] {w : ℕ} (hw : BPF.hasWidth (·≤w)) :
    ∀ n, (BPF n).size ≤ w * (BPF n).depth + 1 := by
  intro n
  grw [(BPF n).size_le_width_mul_depth, show (BPF n).width ≤ w from hw n]

/-- Constant functions are in the `GrowthRate.const` class. -/
theorem GrowthRate.const_mem_const (k : ℕ) : (fun _ ↦ k) ∈ GrowthRate.const := by
  simp only [const, bigO, Pi.one_apply, Nat.cast_one, Asymptotics.isBigO_one_iff]
  use k
  simp

lemma GrowthRate.affine_comp {S : GrowthRate} [LawfulGrowthRate S] {f : ℕ → ℕ} {a b : ℕ} (hf : f ∈ S) :
    (fun n ↦ a * f n + b) ∈ S :=
  GrowthRate.add
    (GrowthRate.const_mul (GrowthRate.const_mem_const a) hf)
    (GrowthRate.const_mem <| GrowthRate.const_mem_const b)

/--
If a branching program family has constant width and polynomial depth, it has polynomial size.
-/
theorem BPFamily.hasSize_poly_of_hasWidth_const_hasDepth_poly (BPF : BPFamily α) [BPF.Finite]
    {w : ℕ} (hw : BPF.hasWidth (·≤w)) (hd : BPF.hasDepth .poly) :
    BPF.hasSize GrowthRate.poly :=
  GrowthRate.mono (GrowthRate.affine_comp hd) (BPF.size_le_bound hw)

/--
If a Barrington program computes a function f with permutation sigma, then its converted branching program computes f.
-/
theorem BarringtonProgram.toBP_computes_of_computes {n : ℕ} (BP : BarringtonProgram (Fin n) (Equiv.Perm (Fin 5)))
    (f : (Fin n → Fin 2) → Fin 2) (σ : Equiv.Perm (Fin 5))
    (hσ0 : σ 0 ≠ 0) (h : BP.computes f σ) :
    (BP.toBP σ (Fin 5)).computes f := by
  rw [LayeredBranchingProgram.computes]
  intro x
  rw [BarringtonProgram.toBP_eval BP σ x hσ0]
  have h_eval : BP.eval x = if f x = 1 then σ else 1 := h.2 x
  rcases Fin.exists_fin_two.mp ⟨f x, rfl⟩ with h | h
  · simp [h_eval, h, hσ0.symm]
  · simp [h_eval, h]

theorem NC1_subset_BPClass : NCi 1 ⊆ BPClass (·≤5) .poly true := by
  intro f ⟨u, hu, cf, hcf⟩
  use BP_of_CircuitFamily cf
  rcases hcf with ⟨hcf_fin, hcf_comp, _, hcf_depth, hcf_gates⟩
  fconstructor
  · apply BP_of_CircuitFamily_Finite
  and_intros
  · apply BarringtonProgram.of_CircuitFamily_computes hcf_comp hcf_gates
  · apply BarringtonProgram.of_CircuitFamily_hasWidth_five
  · apply BarringtonProgram.of_CircuitFamily_hasDepth_poly
    simp_rw [pow_one, GrowthRate.bigO_log2_eq_log] at hcf_depth
    exact hcf_depth
  · intro _
    apply BarringtonProgram.of_CircuitFamily_IsOblivious
