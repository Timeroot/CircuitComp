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
def evalNode {d : Fin (F.depth + 1)} (node : F.nodes d) (xs : inp → α) : α := by
  rcases d with ⟨d, hd⟩
  induction d
  · exact xs (F.nodes_zero ▸ node)
  · rename_i d' ih
    apply (F.gates ⟨d', Nat.succ_lt_succ_iff.mp hd⟩ node).eval
    exact fun node' ↦ ih (Nat.lt_of_succ_lt hd) node'

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

-- @[simp]

/-- Relabel the output type of a `FeedForward` given an `Equiv`. -/
def relabelOut (hF : F.depth ≠ 0) (e : out ≃ a) : FeedForward α inp a :=
  have : NeZero F.depth := ⟨hF⟩
  { depth := F.depth
    nodes k := if k = ⊤ then a else F.nodes k
    gates k n := if hk : k = ⊤ then
        have g := F.gates k (by simp [Fin.top_eq_last, hk] at n ⊢; exact e.symm n)
        ⟨g.op, have gi := g.inputs; fun i ↦ by simp [hk, Fin.top_eq_last, Fin.castSucc] at gi ⊢; exact sorry⟩
      else cast (by simp [hk, Fin.top_eq_last, (Fin.castSucc_lt_last k).ne]) (F.gates k sorry)
    nodes_zero := by simp [hF]
    nodes_last := by simp [hF, Fin.top_eq_last]
  }

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

@[simp]
theorem eval_comp (F : FeedForward α a b) (G : FeedForward α b c) : (G.comp F).eval = G.eval ∘ F.eval := by
  sorry

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

theorem eval_sum {d : ℕ} (f : FeedForward α a b) (g : FeedForward α a₂ b₂) (hf : f.depth = d) (hg : g.depth = d) :
    ∀ (x : a ⊕ a₂ → α), (f.sum g hf hg).eval x = Sum.elim (f.eval (x ∘ .inl)) (g.eval (x ∘ .inr)) := by
  sorry

/-- The cardinal width of a feedforward circuit is the largest number of nodes in any layer. -/
noncomputable def width_card : Cardinal :=
  ⨆ d, Cardinal.mk (F.nodes d)

/-- The size of a feedforward circuit is the total number of gates. Note that if any layer is
infinite, the whole sum will be zero. -/
noncomputable def size : ℕ :=
  Nat.card (@Sigma (Fin F.depth) (fun d ↦ F.nodes d.succ))

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

end FeedForward

open FeedForward

/-- A `CircuitFamily` is a collection of `FeedForward` circuits parameterized by an input size `n`.
The `n`th circuit must have input type `Fin n`, and a `Unit` output. -/
def CircuitFamily (α : Type u) :=
  (n : ℕ) → FeedForward α (Fin n) Unit

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
