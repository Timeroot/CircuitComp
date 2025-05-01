import Mathlib.Data.Fintype.EquivFin

--is there a reason these aren't already simps in mathlib?
@[simp]
theorem setOf_eq_empty_iff {α : Type*} (p : α → Prop) : { x | p x } = ∅ ↔ ∀ x, ¬p x :=
  Set.eq_empty_iff_forall_not_mem

@[simp]
theorem Finset.filter_univ_eq_empty_iff {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ({ x | p x } : Finset α) = ∅ ↔ ∀ x, ¬p x :=
  ⟨by simp [Finset.filter_eq_empty_iff], (by simp [·])⟩

variable {α β ι : Type*} (f : (ι → α) → β)

/-- The essential domain of a function is the set of arguments which, by changing the input,
can change the output. When `Finite ι`, this is equivalent to saying that the function is
fully determined by its values on `EssDomain`. This isn't true when the arity is infinite
however, e.g. the function `f : (ℕ → ℕ) → Bool` that says "does this `ℕ to ℕ` sequence
converge?" has no essential domain, because no individual value in the sequence will change
the output. -/
def Function.EssDomain : Set ι :=
  { i | ∃ x1 x2, (∀ j ≠ i, x1 j = x2 j) ∧ f x1 ≠ f x2 }

instance essDomain_Empty_of_Subsingleton [Subsingleton β] : IsEmpty f.EssDomain := by
  rw [Set.isEmpty_coe_sort]
  ext
  simp only [Function.EssDomain, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and, not_not]
  intros
  apply Subsingleton.elim

instance essDomain_Empty_of_Subsingleton' [Subsingleton α] : IsEmpty f.EssDomain := by
  rw [Set.isEmpty_coe_sort]
  ext
  simp only [Function.EssDomain, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and, not_not]
  intros x1 x2 _
  exact congrArg f (Subsingleton.elim x1 x2)

theorem const_of_essDomain_empty [Nonempty α] [Fintype ι] {f : (ι → α) → β}
    (hf : f.EssDomain = ∅) : ∃ c, ∀ x, f x = c := by
  inhabit α
  suffices ∀ x y, f x = f y by
    use f (fun _ ↦ default)
    exact fun x ↦ this x _
  intro x y
  classical
  generalize hd : ({ i | x i ≠ y i} : Finset ι) = d
  induction d using Finset.induction generalizing x y
  · simp at hd
    exact congrArg f (funext hd)
  rename_i i s hi ih
  let z : ι → α := fun j ↦ if i = j then x j else y j
  have hz : ({ i | x i ≠ z i} : Finset ι) = s := by
    ext j
    by_cases hj : i = j
    · simpa [z, ← hj]
    · simpa [z, hj, eq_comm] using congrArg (j ∈ ·) hd
  refine (ih x z hz).trans ?_
  simp [Function.EssDomain] at hf
  apply hf i
  intro j
  simp +contextual [z, eq_comm]

/-- A function can be reduced to its essential domain: there is a function `g` which only
looks at the essential domain, and agrees with `f`.

As noted in `Function.EssDomain`, this requires the arity `ι` to be finite. As a more technical
caveat, we also need `Nonempty α`: otherwise, if `β` is an empty type and `ι` is not, we can have a
case where f's argument `ι → α` is an empty type and so is `f`'s codomain, but any `g` would need
to take a `f.EssDomain → α` (which is inhabited and in fact `Unique`) to the empty `β`.
-/
theorem exists_comp_on_essDomain [Nonempty α] [Fintype ι] (f : (ι → α) → β) :
    ∃ (g : (f.EssDomain → α) → β), ∀ x, f x = g (x ·) := by
  wlog hi : Nonempty ι
  · rw [not_nonempty_iff] at hi
    use (fun _ ↦ f hi.elim)
    intro
    congr
    apply Subsingleton.elim
  have : Inhabited β := Classical.inhabited_of_nonempty <|
    Nonempty.elim (inferInstance) (fun a ↦ ⟨f (fun _ ↦ a)⟩)
  inhabit α
  --We construct g by agreeing with f on its essential support, and providing a dummy value
  --elsewhere. We prove the property by induction on the number of dummy values we use, which
  --means generalizing to any set containing the essential support.
  suffices ∀ (S : Set ι), [Finite S] → f.EssDomain ⊆ S →
      ∃ (g : (S → α) → β), ∀ x, f x = g (x ·) from
    this f.EssDomain (by rfl)
  intro S hS₁ hS₂
  let _ : DecidableEq ι := Classical.typeDecidableEq ι
  let _ : Fintype S := Fintype.ofFinite _
  let Sf := S.toFinset
  generalize hSc : (Sfᶜ : Finset ι) = Sc
  induction Sc using Finset.induction generalizing S
  · simp [Sf] at hSc
    subst S
    use fun xs ↦ f (fun i ↦ xs ⟨i, by trivial⟩)
    simp only [implies_true]
  unfold Sf at hSc
  clear Sf
  rename_i i s hi ih _
  simp only [← Finset.coe_inj, Finset.coe_compl, Set.coe_toFinset, Finset.coe_insert] at hSc
  rw [← Finset.mem_coe] at hi
  dsimp at ih
  specialize ih sᶜ ?_ ?_
  · apply hS₂.trans
    rw [← compl_compl S, hSc, Set.compl_subset_compl]
    exact Set.subset_insert i ↑s
  · simp
  generalize (↑s : Set ι) = s₀ at *
  clear s
  have hi₂ : i ∈ Sᶜ := by
    have : i ∈ insert i s₀ := by exact Set.mem_insert i s₀
    rwa [← hSc] at this
  have hi₃ : i ∉ f.EssDomain := (hi₂ <| hS₂ ·)
  clear hS₂
  obtain ⟨g₀, hg₀⟩ := ih
  replace hg₀ := funext hg₀
  subst f
  use (fun xs ↦ g₀ fun j ↦ if hj : j = i then default else xs ⟨j, by
    rw [← compl_compl S]
    simpa [hSc, hj, -Subtype.coe_prop] using j.prop
    ⟩)
  simp [Function.EssDomain] at hi₃
  exact fun _ ↦ hi₃ _ _ fun _ ↦ (Eq.symm <| if_neg ·)
