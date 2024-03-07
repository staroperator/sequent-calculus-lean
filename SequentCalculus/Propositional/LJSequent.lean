import SequentCalculus.Propositional.Syntax

namespace Propositional

variable {α : Type u} [DecidableEq α]

@[aesop unsafe]
inductive LJSequent : Context α → Formula α → Nat → Prop where
| ax : LJSequent (Γ, p) p 0
| falseL : LJSequent (Γ, ⊥) p 0
| andL₁ : LJSequent (Γ, p) r k → LJSequent (Γ, p ⋀ q) r (k + 1)
| andL₂ : LJSequent (Γ, q) r k → LJSequent (Γ, p ⋀ q) r (k + 1)
| andR : LJSequent Γ p k → LJSequent Γ q k → LJSequent Γ (p ⋀ q) (k + 1)
| orL : LJSequent (Γ, p) r k → LJSequent (Γ, q) r k → LJSequent (Γ, p ⋁ q) r (k + 1)
| orR₁ : LJSequent Γ p k → LJSequent Γ (p ⋁ q) (k + 1)
| orR₂ : LJSequent Γ q k → LJSequent Γ (p ⋁ q) (k + 1)
| impL : LJSequent Γ p k → LJSequent (Γ, q) r k → LJSequent (Γ, p ⇒ q) r (k + 1)
| impR : LJSequent (Γ, p) q k → LJSequent Γ (p ⇒ q) (k + 1)
| succ : LJSequent Γ p k → LJSequent Γ p (k + 1)

scoped notation:55 Γ " ⊢[" k "] " p:55 => LJSequent Γ p k

namespace LJSequent

open Finset
variable {Γ Δ : Context α} {p q : Formula α}

theorem le : Γ ⊢[k] p → k ≤ k' → Γ ⊢[k'] p := by
  intro h₁ h
  induction h with
  | refl => exact h₁
  | step _ ih => exact succ ih

theorem ax' : p ∈ Γ → Γ ⊢[0] p := by
  intro h
  rw [←add_eq_of_mem h]
  exact ax

theorem negL : Γ ⊢[k] p → Γ, ~ p ⊢[k + 1] ⊥ :=
  (impL · (le falseL (zero_le _)))

theorem negR : Γ, p ⊢[k] ⊥ → Γ ⊢[k + 1] ~ p := impR

theorem trueR : Γ ⊢[1] (⊤ : Formula α) := negR falseL

theorem weakenL : Γ ⊢[k] p → Γ ⊆ Δ → Δ ⊢[k] p := by
  intro h₁ h
  induction' k using Nat.strongRecOn with k ih generalizing Γ Δ p
  cases h₁ with
  | succ h₁ => apply succ; apply ih _ _ _ h <;> aesop
  | ax | falseL | andL₁ | impL =>
    rw [←add_eq_of_mem (h mem_add_self)]
    simp [add_subset_iff] at h; cases h
    constructor <;> apply ih <;> aesop (add safe add_subset_add)
  | andL₂ =>
    rw [←add_eq_of_mem (h mem_add_self)]
    simp [add_subset_iff] at h; cases h
    apply andL₂; apply ih <;> aesop (add safe add_subset_add)
  | orL h₁ h₂ =>
    rw [←add_eq_of_mem (h mem_add_self)]
    simp [add_subset_iff] at h; cases h
    constructor
    · apply ih _ _ h₁ <;> aesop (add safe add_subset_add)
    · apply ih _ _ h₂ <;> aesop (add safe add_subset_add)
  | andR | orR₁ | impR =>
    constructor <;> apply ih <;> aesop (add safe add_subset_add)
  | orR₂ =>
    apply orR₂; apply ih <;> aesop (add safe add_subset_add)

theorem weakenL' : Γ ⊢[k] p → Γ, q ⊢[k] p :=
  (weakenL · subset_add)

theorem consistency : (∅ ⊢[k] (⊥ : Formula α)) → False := by
  intro h
  induction' k using Nat.strongRecOn with k ih
  generalize h₁ : (∅ : Context α) = Γ at h
  cases h <;> exact add_ne_empty (Eq.symm h₁)
  case succ k h => subst h₁; apply ih k <;> aesop

theorem or_inversion : ∅ ⊢[k] p ⋁ ~ p → ∅ ⊢[k] p ∨ ∅ ⊢[k] ~ p := by
  intro h
  induction' k using Nat.strongRecOn with k ih
  generalize h₁ : (∅ : Context α) = Γ at h
  cases h <;> (try cases add_ne_empty (Eq.symm h₁))
  case orR₁ => left; apply succ; assumption
  case orR₂ => right; apply succ; assumption
  case succ h => subst h₁; apply ih at h <;> aesop

open Formula in
theorem no_excluded_middle {a : α} : ∅ ⊢[k] atom a ⋁ ~ atom a → False := by
  intro h
  apply or_inversion at h
  rcases h with h | h
    <;> induction' k using Nat.strongRecOn with k ih
    <;> generalize h₁ : (∅ : Context α) = Γ at h
    <;> cases h <;> (try cases add_ne_empty (Eq.symm h₁))
    <;> subst h₁ <;> rename _ => h
    <;> (try apply ih at h <;> aesop)
  generalize h₁ : (∅, atom a) = Γ at h
  clear ih; rename Nat => k
  induction' k using Nat.strongRecOn with k ih
  cases h
  case succ h => apply ih at h <;> aesop
  all_goals
    rcases (add_eq_add h₁) with h₂ | ⟨h₂, h₃⟩ <;> (try injection h₂)
    simp at h₃

set_option maxHeartbeats 400000
attribute [simp] Nat.add_zero Nat.add_succ Nat.succ_add Nat.lt_succ

theorem cut {Γ : Context α} :
  Γ ⊢[k₁] p → Γ, p ⊢[k₂] q → ∃ k, Γ ⊢[k] q := by
  intro h₁ h₂
  
  induction' h : p.size using Nat.strongRecOn with _ ih₁ generalizing Γ p q k₁ k₂; subst h
  replace ih₁ : ∀ {Γ : Context α} {p' q k₁ k₂},
    Γ ⊢[k₁] p' → Γ, p' ⊢[k₂] q → p'.size < p.size → ∃ k, Γ ⊢[k] q := by
    intros _ _ _ _ _ h₁ h₂ h₃
    exact ih₁ _ h₃ h₁ h₂ rfl
  induction' h : (k₁ + k₂) using Nat.strongRecOn with _ ih₂
    generalizing Γ p q k₁ k₂; subst h
  replace ih₂ : ∀ {Γ q k₁' k₂'},
    Γ ⊢[k₁'] p → Γ, p ⊢[k₂'] q → k₁' + k₂' < k₁ + k₂ → ∃ k, Γ ⊢[k] q := by
    intros _ _ _ _ h₁ h₂ h₃
    apply ih₂ _ h₃ h₁ h₂ _ rfl
    apply ih₁
  
  generalize h : (Γ, p) = Δ at h₂
  have h₁' := h₁
  cases h₁' with simp at *
  | succ h₁' => subst h; rcases ih₂ h₁' h₂ (by simp) with ⟨k, h₃⟩; exists k
  | ax => subst h; rw [add_contraction] at h₂; exists k₂
  | falseL => exists 0; exact falseL
  | @andL₁ Γ p₁ _ k₁ p₂ h₁' =>
    subst h
    apply weakenL' (q := p₁ ⋀ p₂) at h₁'; rw [add_exchange] at h₁'
    apply weakenL' (q := p₁) at h₂; rw [add_exchange] at h₂
    rcases ih₂ h₁' h₂ (by simp) with ⟨k, h₃⟩
    exists k + 1
    rw [←add_contraction]
    exact andL₁ h₃
  | @andL₂ Γ p₂ _ k₁ p₁ h₁' =>
    subst h
    apply weakenL' (q := p₁ ⋀ p₂) at h₁'; rw [add_exchange] at h₁'
    apply weakenL' (q := p₂) at h₂; rw [add_exchange] at h₂
    rcases ih₂ h₁' h₂ (by simp) with ⟨k, h₃⟩
    exists k + 1
    rw [←add_contraction]
    exact andL₂ h₃
  | @orL Γ p₁ _ k₁ p₂ h₁' h₁'' =>
    subst h
    have h₂' := h₂
    apply weakenL' (q := p₁ ⋁ p₂) at h₁'; rw [add_exchange] at h₁'
    apply weakenL' (q := p₁) at h₂; rw [add_exchange] at h₂
    rcases ih₂ h₁' h₂ (by simp) with ⟨k, h₃⟩
    apply weakenL' (q := p₁ ⋁ p₂) at h₁''; rw [add_exchange] at h₁''
    apply weakenL' (q := p₂) at h₂'; rw [add_exchange] at h₂'
    rcases ih₂ h₁'' h₂' (by simp) with ⟨k', h₃'⟩
    exists max k k' + 1
    rw [←add_contraction]
    apply orL
    · apply le h₃; simp
    · apply le h₃'; simp
  | @impL Γ p₁ k₁ p₂ _ h₁' h₁'' =>
    subst h
    apply weakenL' (q := p₁ ⇒ p₂) at h₁''; rw [add_exchange] at h₁''
    apply weakenL' (q := p₂) at h₂; rw [add_exchange] at h₂
    rcases ih₂ h₁'' h₂ (by simp) with ⟨k, h₃⟩
    exists max k₁ k + 1
    rw [←add_contraction]
    apply impL
    · apply weakenL'; apply le h₁'; simp
    · apply le h₃; simp
  | @andR Γ p₁ k₁ p₂ h₁' h₁'' | @orR₁ Γ p₁ k₁ p₂ h₁'
  | @orR₂ Γ p₁ k₁ p₂ h₁' | @impR Γ p₁ p₂ k₁ h₁' =>
    have h₂' := h₂
    cases h₂' with simp at *
    | succ h₂' => subst h; rcases ih₂ h₁ h₂' (by aesop) with ⟨k, h₃⟩; exists k
    | @andR Δ q₁ k₂ q₂ h₂' h₂'' =>
      subst h
      rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
      rcases ih₂ h₁ h₂'' (by simp) with ⟨k', h₃'⟩
      exists max k k' + 1
      apply andR
      · apply le h₃; simp
      · apply le h₃'; simp
    | @orR₁ Δ q₁ k₂ q₂ h₂' =>
      subst h
      rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
      exists k + 1
      exact orR₁ h₃
    | @orR₂ Δ q₁ k₂ q₂ h₂' =>
      subst h
      rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
      exists k + 1
      exact orR₂ h₃
    | @impR Δ q₁ q₂ k₂ h₂' =>
      subst h
      rw [add_exchange] at h₂'
      rcases ih₂ (weakenL' h₁) h₂' (by simp) with ⟨k, h₃⟩
      exists k + 1
      exact impR h₃
    | ax =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · subst h'; exists k₁ + 1
      · exists 0; exact ax' h''
    | falseL =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
      · rw [←add_eq_of_mem h'']; exists 0; exact falseL
    | @andL₁ Δ q₁ _ k₂ q₂ h₂' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply weakenL' (q := q₁) at h₁
          apply weakenL' (q := q₁ ⋀ q₂) at h₂'
          rw [add_exchange] at h₂'
          rw [←h] at h₂'
          rw [add_exchange] at h₂'
          rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
          rcases ih₁ h₁' h₃ (by simp) with ⟨k', h₃'⟩
          exists k'
      · apply weakenL' (q := q₁) at h₁
        apply weakenL' (q := q₁ ⋀ q₂) at h₂'
        rw [add_exchange] at h₂'
        rw [←h] at h₂'
        rw [add_exchange] at h₂'
        rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
        exists k + 1
        rw [←add_eq_of_mem h'']
        exact andL₁ h₃
    | @andL₂ Δ q₂ _ k₂ q₁ h₂' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply weakenL' (q := q₂) at h₁
          apply weakenL' (q := q₁ ⋀ q₂) at h₂'
          rw [add_exchange] at h₂'
          rw [←h] at h₂'
          rw [add_exchange] at h₂'
          rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
          rcases ih₁ h₁'' h₃ (by simp) with ⟨k', h₃'⟩
          exists k'
      · apply weakenL' (q := q₂) at h₁
        apply weakenL' (q := q₁ ⋀ q₂) at h₂'
        rw [add_exchange] at h₂'
        rw [←h] at h₂'
        rw [add_exchange] at h₂'
        rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
        exists k + 1
        rw [←add_eq_of_mem h'']
        exact andL₂ h₃
    | @orL Δ q₁ _ k₂ q₂ h₂' h₂'' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        try case orR₁.orL.inl =>
          subst_vars
          apply weakenL' (q := q₁ ⋁ q₂) at h₂'
          rw [add_exchange] at h₂'
          rw [←h] at h₂'
          rw [add_exchange] at h₂'
          rcases ih₂ (weakenL' h₁) h₂' (by simp) with ⟨k, h₃⟩
          rcases ih₁ h₁' h₃ (by simp) with ⟨k', h₃'⟩
          exists k'
        all_goals
          subst_vars
          apply weakenL' (q := q₁ ⋁ q₂) at h₂''
          rw [add_exchange] at h₂''
          rw [←h] at h₂''
          rw [add_exchange] at h₂''
          rcases ih₂ (weakenL' h₁) h₂'' (by simp) with ⟨k, h₃⟩
          rcases ih₁ h₁' h₃ (by simp) with ⟨k', h₃'⟩
          exists k'
      · apply weakenL' (q := q₁ ⋁ q₂) at h₂'
        rw [add_exchange] at h₂'
        rw [←h] at h₂'
        rw [add_exchange] at h₂'
        rcases ih₂ (weakenL' h₁) h₂' (by simp) with ⟨k, h₃⟩
        apply weakenL' (q := q₁ ⋁ q₂) at h₂''
        rw [add_exchange] at h₂''
        rw [←h] at h₂''
        rw [add_exchange] at h₂''
        rcases ih₂ (weakenL' h₁) h₂'' (by simp) with ⟨k', h₃'⟩
        exists max k k' + 1
        rw [←add_eq_of_mem h'']
        apply orL
        · apply le h₃; simp
        · apply le h₃'; simp
    | @impL Δ q₁ k₂ q₂ _ h₂' h₂'' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply weakenL' (q := q₁ ⇒ q₂) at h₂'
          rw [←h] at h₂'
          rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
          rcases ih₁ h₃ h₁' (by simp) with ⟨k, h₃⟩
          apply weakenL' (q := q₁ ⇒ q₂) at h₂''
          rw [add_exchange] at h₂''
          rw [←h] at h₂''
          rw [add_exchange] at h₂''
          rcases ih₂ (weakenL' h₁) h₂'' (by simp) with ⟨k', h₃'⟩
          rcases ih₁ h₃ h₃' (by simp) with ⟨k'', h₃''⟩
          exists k''
      · apply weakenL' (q := q₁ ⇒ q₂) at h₂'
        rw [←h] at h₂'
        rcases ih₂ h₁ h₂' (by simp) with ⟨k, h₃⟩
        apply weakenL' (q := q₁ ⇒ q₂) at h₂''
        rw [add_exchange] at h₂''
        rw [←h] at h₂''
        rw [add_exchange] at h₂''
        rcases ih₂ (weakenL' h₁) h₂'' (by simp) with ⟨k', h₃'⟩
        exists max k k' + 1
        rw [←add_eq_of_mem h'']
        apply impL
        · apply le h₃; simp
        · apply le h₃'; simp



end LJSequent

end Propositional
