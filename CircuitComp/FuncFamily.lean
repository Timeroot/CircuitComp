import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Card

import CircuitComp.EssDomain

/-!

Define a family of functions, or `FuncFamily`, as a function of arity `n`
from `α` to itself. This is the circuit-complexity equivalent of `Language`
when `α` has cardinality two (so that one value represents ACCEPT and one
REJECT), otherwise one can think of it as describing function problems.

Define it here, give the correspondence to languages, and define basic
important problems.

-/

/-- A Sigma type over functions of varying arity from α to α. -/
abbrev FuncFamily (α : Type*) := (n : ℕ) → (Fin n → α) → α

namespace FuncFamily

variable {α β : Type*}

open Classical in
/-- A function family over booleans can be viewed as a language, where the output
value of `true` corresponds to the string being in the language. -/
noncomputable def toLanguage : FuncFamily Bool ≃ Language Bool where
  toFun f := { s | f s.length s.get }
  invFun l := fun n xs ↦ decide (List.ofFn xs ∈ l)
  left_inv := by
    intro fs
    ext n f
    have := List.length_ofFn (f := f)
    dsimp
    rw [Set.mem_setOf]
    simp only [Bool.decide_eq_true]
    congr
    refine Function.hfunext ?_ ?_
    · congr
    · intros
      rw [List.get_ofFn, Fin.cast]
      congr
  right_inv := by
    intro
    ext
    rw [Set.mem_setOf]
    simp

/-- Lift an equivalence `α ≃ β` to an equivalence `FuncFamily α ≃ FuncFamily β`. -/
@[simps]
def onEquiv (e : α ≃ β) : FuncFamily α ≃ FuncFamily β where
  toFun fn n x := e <| fn n <| e.symm ∘ x
  invFun fn n x := e.symm <| fn n <| e ∘ x
  left_inv _ := by simp [← Function.comp_assoc]
  right_inv _ := by simp [← Function.comp_assoc]

/-- The problem AND: Compute the logical AND of the input bits. -/
def AND : FuncFamily (Fin 2) :=
  fun _ xs ↦ ∏ i, xs i

/-- The problem PARITY: Compute the parity of the input bits. -/
def PARITY : FuncFamily (Fin 2) :=
  fun _ xs ↦ ∑ i, xs i

/-- The "AND" problem has an essential dependence of all inputs. -/
theorem AND_EssDomain : ∀ n, (AND n).EssDomain = .univ := by
  intro n
  ext i
  simp only [Function.EssDomain, ne_eq, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  use (fun _ ↦ 1), (fun j ↦ if i = j then 0 else 1)
  constructor
  · simp +contextual [eq_comm]
  · simp [AND]

end FuncFamily
