import CircuitComp.BranchingProgram.Basic

/-!
Canonical branching program for a function F. It queries variables in a fixed order
and stores the values in the nodes. It branches exponentially wide.
-/

open LayeredBranchingProgram

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w} [Fintype α] (F : (α → β) → γ)

/--
Construct a canonical branching program for a function F. It queries variables in a fixed order
and stores the values in the nodes. It branches exponentially wide.
-/
def canonicalBP : LayeredBranchingProgram α β γ where
  depth := Fintype.card α
  nodes i := Fin i → β
  nodeVar {i} _ := (Fintype.equivFin α).symm ⟨i, i.is_lt⟩
  edges {i} f b j := if h : j.val < i.val then f ⟨j.val, h⟩ else b
  startUnique := {
    default := Fin.elim0,
    uniq := fun _ ↦ funext fun i ↦ Fin.elim0 i
  }
  retVals f := F (f ∘ Fintype.equivFin α)

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
