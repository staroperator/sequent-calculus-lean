import Mathlib.Data.Finset.Basic

namespace Finset

variable {α : Type u} [DecidableEq α]

def add (s : Finset α) (x : α) := insert x s
infixl:60 (priority := low) ",, " => Finset.add

variable {s t : Finset α} {a b : α}

@[simp] theorem mem_add : a ∈ s,, b ↔ a = b ∨ a ∈ s := mem_insert
theorem mem_add_self : a ∈ s,, a := mem_insert_self _ _
theorem subset_add : s ⊆ s,, a := subset_insert _ _
theorem mem_of_mem_add_of_ne (h₁ : a ∈ s,, b) (h₂ : a ≠ b) : a ∈ s :=
  mem_of_mem_insert_of_ne h₁ h₂
theorem add_eq_of_mem (h : a ∈ s) : s,, a = s := insert_eq_of_mem h
theorem add_subset (h₁ : a ∈ t) (h₂ : s ⊆ t) : s,, a ⊆ t := insert_subset h₁ h₂
theorem add_ne_empty : s,, a ≠ ∅ := insert_ne_empty _ _
theorem add_subset_iff : s,, a ⊆ t ↔ a ∈ t ∧ s ⊆ t := insert_subset_iff
theorem add_subset_add (h : s ⊆ t) : s,, a ⊆ t,, a := insert_subset_insert _ h

theorem add_contraction : s,, a,, a = s,, a := insert_idem _ _
theorem add_exchange : s,, a,, b = s,, b,, a := by ext r; simp; aesop

theorem add_eq_add : s,, a = t,, b → a = b ∨ a ∈ t ∧ b ∈ s := by
  intro h
  by_cases h₁ : a = b
  · left; exact h₁
  · right; constructor
    · apply mem_of_mem_add_of_ne _ h₁; rw [←h]; simp
    · apply mem_of_mem_add_of_ne _ (Ne.symm h₁); rw [h]; simp



end Finset
