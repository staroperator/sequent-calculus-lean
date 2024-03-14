import Mathlib.Data.Finset.Basic

namespace Finset

variable {α : Type u} [DecidableEq α]

def append (s : Finset α) (x : α) := insert x s
infixl:60 ",, " => Finset.append

variable {s t : Finset α} {a b : α}

@[simp] theorem mem_append : a ∈ s,, b ↔ a = b ∨ a ∈ s := mem_insert
theorem mem_append_self : a ∈ s,, a := mem_insert_self _ _
theorem subset_append : s ⊆ s,, a := subset_insert _ _
theorem mem_of_mem_append_of_ne (h₁ : a ∈ s,, b) (h₂ : a ≠ b) : a ∈ s :=
  mem_of_mem_insert_of_ne h₁ h₂
theorem append_eq_of_mem (h : a ∈ s) : s,, a = s := insert_eq_of_mem h
theorem append_subset (h₁ : a ∈ t) (h₂ : s ⊆ t) : s,, a ⊆ t := insert_subset h₁ h₂
theorem append_ne_empty : s,, a ≠ ∅ := insert_ne_empty _ _
theorem append_subset_iff : s,, a ⊆ t ↔ a ∈ t ∧ s ⊆ t := insert_subset_iff
theorem append_subset_append (h : s ⊆ t) : s,, a ⊆ t,, a := insert_subset_insert _ h

theorem append_contraction : s,, a,, a = s,, a := insert_idem _ _
theorem append_exchange : s,, a,, b = s,, b,, a := by ext r; simp; aesop

theorem append_eq_append : s,, a = t,, b → a = b ∨ a ∈ t ∧ b ∈ s := by
  intro h
  by_cases h₁ : a = b
  · left; exact h₁
  · right; constructor
    · apply mem_of_mem_append_of_ne _ h₁; rw [←h]; simp
    · apply mem_of_mem_append_of_ne _ (Ne.symm h₁); rw [h]; simp

end Finset
