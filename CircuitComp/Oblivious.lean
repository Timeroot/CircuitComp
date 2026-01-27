import CircuitComp.BranchingProgram

/-!

Every branching program can be converted to an oblivious branching program
(`LayeredBranchingProgram.IsOblivious`).
-/

open LayeredBranchingProgram

noncomputable section

/-- An unlayered branching program, represented as a DAG. -/
structure BranchingProgram (α : Type u) (β : Type v) (γ : Type w) where
  nodes : Type v
  start : nodes
  info : nodes → Sum γ (α × (β → nodes))
  /-- The relation `child` is well-founded, ensuring no infinite paths. -/
  wellFounded : WellFounded (fun v u ↦ ∃ var next val, info u = .inr (var, next) ∧ next val = v)

/--
Evaluation for `BranchingProgram` starting from a specific node.
-/
def BranchingProgram.evalAt {α β γ} (P : BranchingProgram α β γ) (x : α → β) (u : P.nodes) : γ :=
  P.wellFounded.fix (fun u ih ↦
    match h : P.info u with
    | .inl res => res
    | .inr (var, next) => ih (next (x var)) ⟨var, next, x var, h, rfl⟩
  ) u

/--
Evaluation for `BranchingProgram`.
-/
def BranchingProgram.eval {α β γ} (P : BranchingProgram α β γ) (x : α → β) : γ :=
  P.evalAt x P.start

/--
Conversion from `LayeredBranchingProgram` to `BranchingProgram`.
-/
noncomputable def LayeredBranchingProgram.toBranchingProgram {α β γ} (P : LayeredBranchingProgram α β γ) :
    BranchingProgram α β γ :=
  { nodes := Sigma P.nodes
    start := ⟨0, P.start⟩
    info := fun ⟨i, u⟩ ↦
      i.lastCases
        (fun u ↦ .inl (P.retVals u))
        (fun j u ↦ .inr (P.nodeVar u, fun b ↦ ⟨j.succ, P.edges u b⟩))
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
        exact ih (P.edges u x)
  }

/--
Evaluation for `LayeredBranchingProgram` starting from a specific layer and node.
-/
def LayeredBranchingProgram.evalFrom {α β γ} (P : LayeredBranchingProgram α β γ) (x : α → β) (i : Fin P.depth.succ) (u : P.nodes i) : γ :=
  if h : i = Fin.last P.depth then
    P.retVals (h ▸ u)
  else
    let i' : Fin P.depth := i.castPred h
    let u' : P.nodes i'.castSucc := (Fin.castSucc_castPred i h).symm ▸ u
    let next_node := P.edges u' (x (P.nodeVar u'))
    LayeredBranchingProgram.evalFrom P x i'.succ next_node
termination_by P.depth - i
decreasing_by
-- Since $i$ is not the last element, we have $i < P.depth$.
have h_i_lt_depth : i.val < P.depth := by
  exact lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using h );
exact Nat.sub_lt_sub_left ( by aesop ) ( by aesop )

/--
`evalFrom` starting at the node reached by `evalLayer` yields the same result as `eval`.
-/
@[simp]
theorem LayeredBranchingProgram.evalFrom_evalLayer_eq_eval {α β γ} (P : LayeredBranchingProgram α β γ) (x : α → β) (i : Fin P.depth.succ) :
    P.evalFrom x i (P.evalLayer i x) = P.eval x := by
  induction' i using Fin.reverseInduction with i ihes;
  · unfold LayeredBranchingProgram.eval;
    unfold evalFrom;
    simp +zetaDelta at *;
  · unfold evalFrom; aesop;

/--
`evalAt` on the converted DAG equals `evalFrom` on the layered program.
-/
theorem LayeredBranchingProgram.toBranchingProgram_evalAt_eq_evalFrom {α β γ} (P : LayeredBranchingProgram α β γ) (x : α → β) (i : Fin P.depth.succ) (u : P.nodes i) :
    P.toBranchingProgram.evalAt x ⟨i, u⟩ = P.evalFrom x i u := by
  induction' i using Fin.reverseInduction with i IH;
  · rw [ evalFrom ];
    unfold BranchingProgram.evalAt;
    rw [ WellFounded.fix_eq ];
    unfold toBranchingProgram; aesop;
  · unfold BranchingProgram.evalAt LayeredBranchingProgram.evalFrom;
    convert IH ( P.edges u ( x ( P.nodeVar u ) ) ) using 1;
    · unfold BranchingProgram.evalAt;
      rw [ WellFounded.fix_eq ];
      unfold toBranchingProgram; simp +decide ;
      simp +decide [ Fin.lastCases ];
      rw [ Fin.reverseInduction_castSucc ];
    · aesop

/-
The DAG conversion from `LayeredBranchingProgram` to `BranchingProgram` preserves semantics.
-/
@[simp]
theorem LayeredBranchingProgram.toBranchingProgram_eval {α β γ} (P : LayeredBranchingProgram α β γ) :
    P.toBranchingProgram.eval = P.eval := by
  funext x
  convert ← LayeredBranchingProgram.toBranchingProgram_evalAt_eq_evalFrom P x 0 P.start
  exact LayeredBranchingProgram.evalFrom_evalLayer_eq_eval P x 0
