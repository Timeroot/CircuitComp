import CircuitComp.BranchingProgram.Basic
import CircuitComp.ForMathlib

/-!
Proof that every Boolean function can be computed by branching program of width 3 and depth O(2^n).
This generalizes appropriately (with a larger width)to other types, with a finite number of
values for each input and a finite number of outputs.
-/

open LayeredBranchingProgram

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty β] (F : (α → β) → γ)

/--
Construct a think branching program for a function F. It keeps constant width but
has exponential depth.
-/
def thinBP : LayeredBranchingProgram α β γ :=
  letI a := Fintype.card α
  letI b := Fintype.card β
  letI c := Fintype.card γ
  haveI : NeZero c := ⟨(Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'⟩
  letI ea := Fintype.equivFin α
  letI eb := Fintype.equivFin β
  letI ec := Fintype.equivFin γ
  -- Map the numbers `b ^ a` to strings of `a` many β's. Used for indexing the layers.
  letI eab : Fin (b ^ a) → α → β :=
    (ea.symm.arrowCongr eb.symm) ∘ finFunctionFinEquiv.symm
  letI γ0 := ec.symm 0 --one particular value of γ
  { depth := a * b ^ a
    --Nodes are 2 special nodes, plus one more for each γ ... except for γ0.
    --We run through checks of each length-α string of β's, staying at (.inl 0) as long
    --as the check is passing, and failing to (.inl 1) if it fails. If we pass the
    --check, we branch to the corresponding γ node. Unless it's γ0, in which case we go
    --continue on (.inl 0). This special handling of γ0 only gets a reduction in width of 1,
    --but that's the difference between showing every Boolean function can be computed in width 3
    --and showing it can be computed in width 4, which is enough to care about!
    nodes i := if i = 0 then PUnit else ULift (Fin 2 ⊕ Fin (c - 1))
    nodeVar {i} _ := ea.symm ⟨i % a, Nat.mod_lt i Fintype.card_pos⟩
    edges {i} f j := by
      split_ifs with h₁
      · simp at h₁
      --The first layer is treated the same (.inl 0) on any other layer.
      if h_first : i.val = 0 ∨ (∃ h, f = cast (if_neg h).symm (ULift.up (.inl 0))) then
        -- This is (.inl 0). Continue a check, unless we're finishing a check in which case
        -- we branch to the appropriate output node.
        let nextβ := eab (⟨i.val / a, Nat.div_lt_of_lt_mul <| by omega⟩) (ea.symm ⟨i % a, Nat.mod_lt i Fintype.card_pos⟩)
        if nextβ = j then
          --The check passed. Continue on (.inl 0), unless we're at the end of the check.
          if i.val % a = a - 1 then
            --Get the output γ value from `F` and branch to the appropriate (.inr) node. But if it's γ0,
            -- we stay on (.inl 0) instead.
            let γOut := F (eab (⟨i.val / a, Nat.div_lt_of_lt_mul <| by omega⟩))
            if hγOut : γOut = γ0 then
              exact .up (.inl 0)
            else
              exact .up (.inr ⟨ec γOut - 1,
                have : (ec γOut).val ≠ 0 := fun _ ↦ hγOut <| ec.injective (by aesop)
                by omega⟩)
          else
            --The check is continuing. Continue on (.inl 0).
            exact .up (.inl 0)
        else
          --The check failed. Continue on (.inl 1), unless that was the end of the check in which case
          -- we stay on (.inl 0) for the next check immediately.
          exact if i.val % a = a - 1 then
            --The check failed at the end. Reset back to (.inl 0) for the next check immediately.
            .up (.inl 0)
          else
            .up (.inl 1)
      else
      have hf₁ : ¬i.castSucc = 0 := (h_first <| .inl <| Fin.ext_iff.mp ·)
      revert f
      rw! [if_neg hf₁]
      intro f h_first
      rcases hf : f.down with (_ | _) | val
      · --This is impossible because of h_first
        exfalso
        exact (show f ≠ .up (.inl 0) from (h_first <| .inr ⟨hf₁, ·⟩)) (by ext; simpa)
      · -- This is (.inl 1). Do nothing and stay, unless we just finished a check and so
        -- we reset back to (.inl 0).
        exact if i.val % a = a - 1 then
          .up (.inl 0)
        else
          .up (.inl 1)
      · -- We're on a γ-valued node. Continue and keep this value.
        exact .up (.inr val)
    startUnique := {
      default := PUnit.unit,
      uniq := by simp
    }
    retVals f := by
      split_ifs at f with h
      · --Impossible
        exfalso
        simp +zetaDelta at h
      · rcases f.down with _ | val
        · exact γ0
        · exact ec.symm ⟨val + 1, by omega⟩
  }


instance thinBP_Finite [Fintype β] : (thinBP F).Finite where
  finite i := by
    dsimp [thinBP]
    split
    · infer_instance
    · infer_instance

theorem thinBP_IsOblivious : (thinBP F).IsOblivious :=
  fun _ _ _ ↦ rfl

theorem thinBP_width : (thinBP F).width = Fintype.card γ + 1 := by
  dsimp [thinBP, width]
  apply le_antisymm
  · refine ciSup_le (fun i ↦ ?_)
    split
    · simp
    · have : Fintype.card γ ≠ 0 := by
        exact (Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'
      grind [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_sum, Fintype.card_fin]
  · refine le_trans ?_ (le_ciSup ?_ ⟨Fintype.card α * Fintype.card β ^ Fintype.card α, ?_⟩)
    · simp only [lt_add_iff_pos_right, zero_lt_one, Fin.mk_eq_zero, mul_eq_zero,
      Fintype.card_ne_zero, Nat.pow_eq_zero]
      grind [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_sum, Fintype.card_fin]
    · simp
    · simp

-------------
--Proving the correctness of `thinBP`.
section thinBP_proof

instance thinBP_depth_pos : NeZero (thinBP F).depth := by
  constructor
  rw [thinBP]
  positivity

noncomputable def thinBP_eab : Fin (Fintype.card β ^ Fintype.card α) ≃ (α → β) :=
  let ea := Fintype.equivFin α
  let eb := Fintype.equivFin β
  finFunctionFinEquiv.symm.trans (ea.symm.arrowCongr eb.symm)

abbrev thinBP_index : (α → β) ≃ Fin (Fintype.card β ^ Fintype.card α) :=
  thinBP_eab.symm

/-- Auxiliary predicate for `thinBP_CorrectState`: does the first `pos` symbols of `x` match
the target string defined by `k`? -/
def thinBP_match (k : Fin (Fintype.card β ^ Fintype.card α)) (pos : ℕ)
    (h_pos : pos ≤ Fintype.card α) (x : α → β) : Prop :=
  let target := thinBP_eab (α := α) (β := β) k
  let ea := Fintype.equivFin α
  ∀ j : Fin pos, x (ea.symm ⟨j, by omega⟩) = target (ea.symm ⟨j, by omega⟩)

omit [Nonempty α] [Nonempty β] in
lemma thinBP_match_zero (k : Fin (Fintype.card β ^ Fintype.card α)) (x : α → β) :
    thinBP_match k 0 (by omega) x :=
  fun j ↦ by cases j; trivial

omit [Nonempty α] [Nonempty β] in
lemma thinBP_match_succ (k : Fin (Fintype.card β ^ Fintype.card α)) (pos : ℕ) (h_pos : pos + 1 ≤ Fintype.card α) (x : α → β) :
    thinBP_match k (pos + 1) h_pos x ↔
    thinBP_match k pos (by omega) x ∧
    x ((Fintype.equivFin α).symm ⟨pos, by omega⟩) =
      thinBP_eab k ((Fintype.equivFin α).symm ⟨pos, by omega⟩) := by
  unfold thinBP_match
  constructor
  · exact fun h ↦ ⟨fun j ↦ h ⟨j, by omega⟩, h ⟨pos, by omega⟩⟩
  · exact fun h j ↦ by cases j using Fin.lastCases <;> simp [*]

omit [Nonempty α] [Nonempty β] in
lemma thinBP_match_card (k : Fin (Fintype.card β ^ Fintype.card α)) (x : α → β) :
    thinBP_match k (Fintype.card α) (by omega) x ↔ thinBP_index x = k := by
  constructor <;> intro h
  · have h_eq : x = thinBP_eab k := by
      ext a
      have := h (Fintype.equivFin α a)
      simp_all
    simp [h_eq]
  · simp [← h, thinBP_match]

open Classical in
/-- The state of the BP at a node `s` when running `x`. We'll inductively prove this claim. -/
def thinBP_CorrectState (i : Fin ((thinBP F).depth + 1)) (x : α → β) (s : (thinBP F).nodes i) : Prop :=
  if h : i.val = 0 then
    HEq s PUnit.unit
  else
    let a := Fintype.card α
    let b := Fintype.card β
    let c := Fintype.card γ
    haveI : NeZero c := ⟨(Fintype.card_pos_iff.mpr ⟨F (fun _ ↦ Classical.arbitrary β)⟩).ne'⟩
    let k := (i : ℕ) / a
    let pos := (i : ℕ) % a
    let idx := thinBP_index x
    let ec := Fintype.equivFin γ
    let γ0 := ec.symm 0
    let s' : ULift (Fin 2 ⊕ Fin (c - 1)) := cast (by
      dsimp [thinBP]
      rw [if_neg]
      intro h_eq
      apply h
      exact Fin.ext_iff.mp h_eq
    ) s
    if h_found : idx < k ∧ F x ≠ γ0 then
      s' = ULift.up (Sum.inr (Fin.mk ((ec (F x)).val - 1) (by
        have : F x ≠ ec.symm 0 := h_found.2
        have : ec (F x) ≠ 0 := by
          intro h_eq
          apply this
          rw [← h_eq, Equiv.symm_apply_apply]
        have h_val : (ec (F x)).val ≠ 0 := by
          intro h
          apply this
          ext
          exact h
        have h_lt : (ec (F x)).val < c := (ec (F x)).is_lt
        omega)))
    else if hk : k < b ^ a then
      if thinBP_match (Fin.mk k hk) pos (le_of_lt (Nat.mod_lt i Fintype.card_pos)) x then
        s' = ULift.up (Sum.inl 0)
      else
        s' = ULift.up (Sum.inl 1)
    else
      s' = ULift.up (Sum.inl 0)

theorem thinBP_CorrectState_zero {s} (x : α → β) :
    thinBP_CorrectState F 0 x s := by
  simp only [thinBP_CorrectState, heq_eq_eq]
  apply Subsingleton.elim

theorem thinBP_CorrectState_one (x : α → β) :
    thinBP_CorrectState F 1 x (evalLayer (thinBP F) 1 x) := by
  simp [thinBP_CorrectState, (thinBP_depth_pos F).out]
  sorry

theorem thinBP_CorrectState_succ {n} (x : α → β) :
    thinBP_CorrectState F n x (evalLayer (thinBP F) n x) := by
  induction n using Fin.inductionOn
  · exact thinBP_CorrectState_zero F x
  rename_i n ih
  by_cases h : n = 0
  · subst n
    rw [Fin.succ_zero_eq_one']
    exact thinBP_CorrectState_one F x
  --Induction
  sorry

theorem thinBP_computes : (thinBP F).computes F := by
  intro x
  rw [eval]
  have h := thinBP_CorrectState_succ F (n := .last _) x
  have h_ge : Fintype.card β ^ Fintype.card α ≤ (thinBP F).depth / Fintype.card α := by
    simp [thinBP]
  simp [thinBP_CorrectState, (thinBP_depth_pos F).out, h_ge.not_gt] at h
  split at h
  · rename_i h₂
    rw [cast_comm] at h
    rw [h]
    simp only [thinBP, eq_mp_eq_cast, cast_cast, cast_eq]
    rw! [Nat.sub_one_add_one]
    · simp
    replace h₂ := h₂.right
    contrapose! h₂
    rw [Equiv.eq_symm_apply]
    have _ : Nonempty γ := ⟨F (fun _ ↦ Nonempty.some ‹_›)⟩
    exact Fin.val_eq_zero_iff.mp h₂
  · rename_i h₂
    push_neg at h₂
    rw [cast_comm] at h
    rw [h]
    have h' : Fin.last (Fintype.card α * Fintype.card β ^ Fintype.card α) ≠ 0 := by
      simp
    simp only [thinBP, eq_mp_eq_cast, cast_cast, cast_eq, h', reduceDIte]
    rw [h₂]
    exact Fin.val_lt_of_le (thinBP_index x) h_ge

end thinBP_proof
------------

/-- Every function can be computed by an oblivious branching program
of exponential size and constant width. -/
theorem computes_const_width :
    ∃ (P : LayeredBranchingProgram α β γ) (_ : P.Finite),
      P.computes F ∧
      P.IsOblivious ∧
      P.width = Fintype.card γ + 1 ∧
      P.depth = Fintype.card α * (Fintype.card β ^ Fintype.card α) := by
  have _ : Nonempty γ := ⟨ F (fun _ ↦ Nonempty.some ‹_›) ⟩
  use thinBP F, thinBP_Finite F
  and_intros
  · exact thinBP_computes F
  · exact thinBP_IsOblivious F
  · rw [thinBP_width]
  · rfl

/-- A boolean function can be computed in O(n * 2^n) depth and width 3.-/
theorem computes_bool_width_3 (F : (α → Bool) → Bool) :
    ∃ (P : LayeredBranchingProgram α Bool Bool) (_ : P.Finite),
      P.computes F ∧
      P.IsOblivious ∧
      P.width = 3 ∧
      P.depth = Fintype.card α * 2 ^ Fintype.card α :=
  computes_const_width F
