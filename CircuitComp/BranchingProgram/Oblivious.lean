import CircuitComp.BranchingProgram.Basic

/-!

Every branching program can be converted to an oblivious branching program
(`LayeredBranchingProgram.IsOblivious`).

First we show that a `SkipBranchingProgram` can be converted to an oblivious branching program,
without increasing width (but with an increase in depth). Then we show that we can convert
this back to a LayeredBranchingProgram without increasing width, and while keeping it oblivious.
-/

noncomputable section

namespace SkipBranchingProgram

variable {α : Type u} {β : Type v} {γ : Type w} [Fintype α] (P : SkipBranchingProgram α β γ)

theorem toLayered_width [P.Finite] : P.toLayered.width = P.width := by
  admit

theorem toLayered_IsOblivious (h : P.IsOblivious) : P.toLayered.IsOblivious := by
  admit

namespace toOblivious

/-- Node type at depth `t` in `SkipBranchingProgram.toOblivious`. -/
def ObliviousNodes (t : Fin (P.depth * Fintype.card α + 1)) : Type v :=
  let k := Fintype.card α
  let E := Fintype.equivFin α
  if h : t < P.depth * k then
    let i : Fin P.depth := ⟨t / k, Nat.div_lt_of_lt_mul <| by linarith⟩
    let j : Fin k := ⟨t % k, Nat.mod_lt _ <| by contrapose! h; simp_all⟩
    { u : P.nodes i.castSucc // E (P.nodeVar u) ≥ j }
  else
    P.nodes (Fin.last P.depth)

/-- Variables read at depth `t` in `SkipBranchingProgram.toOblivious`. -/
def ObliviousNodeVar (t : Fin (P.depth * Fintype.card α)) : α :=
  let k := Fintype.card α
  let E := Fintype.equivFin α
  E.symm ⟨t % k, Nat.mod_lt _ <|
    pos_of_mul_pos_right t.pos (Nat.zero_le _)⟩
