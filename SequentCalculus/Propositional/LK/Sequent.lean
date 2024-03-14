import SequentCalculus.Propositional.Syntax

namespace Propositional.LK

variable {α : Type u} [DecidableEq α]

@[aesop unsafe]
inductive Sequent : Context α → Context α → Prop where
| ax : Sequent (Γ,, p) (Δ,, p)
| falseL : Sequent (Γ,, ⊥) Δ
| andL₁ : Sequent (Γ,, p) Δ → Sequent (Γ,, p ⋀ q) Δ
| andL₂ : Sequent (Γ,, q) Δ → Sequent (Γ,, p ⋀ q) Δ
| andR : Sequent Γ (Δ,, p) → Sequent Γ (Δ,, q) → Sequent Γ (Δ,, p ⋀ q)
| orL : Sequent (Γ,, p) Δ → Sequent (Γ,, q) Δ → Sequent (Γ,, p ⋁ q) Δ
| orR₁ : Sequent Γ (Δ,, p) → Sequent Γ (Δ,, p ⋁ q)
| orR₂ : Sequent Γ (Δ,, q) → Sequent Γ (Δ,, p ⋁ q)
| impL : Sequent Γ (Δ,, p) → Sequent (Γ,, q) Δ → Sequent (Γ,, p ⇒ q) Δ
| impR : Sequent (Γ,, p) (Δ,, q) → Sequent Γ (Δ,, p ⇒ q)
scoped infix:55 " ⊢ " => Sequent
scoped notation:55 Γ " ⊬ " p:55 => ¬ (Γ ⊢ p)

@[aesop unsafe]
inductive HSequent : Context α → Context α → Nat → Prop where
| ax : HSequent (Γ,, p) (Δ,, p) 0
| falseL : HSequent (Γ,, ⊥) Δ 0
| andL₁ : HSequent (Γ,, p) Δ k → HSequent (Γ,, p ⋀ q) Δ (k + 1)
| andL₂ : HSequent (Γ,, q) Δ k → HSequent (Γ,, p ⋀ q) Δ (k + 1)
| andR : HSequent Γ (Δ,, p) k → HSequent Γ (Δ,, q) k → HSequent Γ (Δ,, p ⋀ q) (k + 1)
| orL : HSequent (Γ,, p) Δ k → HSequent (Γ,, q) Δ k → HSequent (Γ,, p ⋁ q) Δ (k + 1)
| orR₁ : HSequent Γ (Δ,, p) k → HSequent Γ (Δ,, p ⋁ q) (k + 1)
| orR₂ : HSequent Γ (Δ,, q) k → HSequent Γ (Δ,, p ⋁ q) (k + 1)
| impL : HSequent Γ (Δ,, p) k → HSequent (Γ,, q) Δ k → HSequent (Γ,, p ⇒ q) Δ (k + 1)
| impR : HSequent (Γ,, p) (Δ,, q) k → HSequent Γ (Δ,, p ⇒ q) (k + 1)
| succ : HSequent Γ Δ k → HSequent Γ Δ (k + 1)
scoped notation:55 Γ " ⊢[" k "] " p:55 => HSequent Γ p k

variable {Γ Γ' Δ Δ' : Context α} {p q : Formula α}

open Finset

namespace HSequent

theorem sequent : Γ ⊢[k] Δ → Γ ⊢ Δ := by
  intro h
  induction h <;> aesop

theorem le : Γ ⊢[k] Δ → k ≤ k' → Γ ⊢[k'] Δ := by
  intro h h₁
  induction h₁ <;> aesop

theorem weakenL : Γ ⊢[k] Δ → Γ ⊆ Γ' → Γ' ⊢[k] Δ := by
  intro h₁ h
  induction' k using Nat.strongRecOn with k ih generalizing Γ Γ' Δ
  cases h₁ with
  | succ h₁ => apply succ; apply ih _ _ _ h <;> aesop
  | ax | falseL | andL₁ | impL =>
    rw [←append_eq_of_mem (h mem_append_self)]
    simp [append_subset_iff] at h; cases h
    constructor <;> apply ih <;> (try apply append_subset_append) <;> aesop
  | andL₂ =>
    rw [←append_eq_of_mem (h mem_append_self)]
    simp [append_subset_iff] at h; cases h
    apply andL₂; apply ih <;> (try apply append_subset_append) <;> aesop
  | orL h₁ h₂ =>
    rw [←append_eq_of_mem (h mem_append_self)]
    simp [append_subset_iff] at h; cases h
    constructor
    · apply ih _ _ h₁ <;> (try apply append_subset_append) <;> aesop
    · apply ih _ _ h₂ <;> (try apply append_subset_append) <;> aesop
  | andR | orR₁ | impR =>
    constructor <;> apply ih <;> (try apply append_subset_append) <;> aesop
  | orR₂ =>
    apply orR₂; apply ih <;> (try apply append_subset_append) <;> aesop

theorem weakenL' : Γ ⊢[k] Δ → Γ,, p ⊢[k] Δ :=
  (weakenL · subset_append)

theorem weakenR : Γ ⊢[k] Δ → Δ ⊆ Δ' → Γ ⊢[k] Δ' := by
  intro h₁ h
  induction' k using Nat.strongRecOn with k ih generalizing Γ Δ Δ'
  cases h₁ with
  | succ h₁ => apply succ; apply ih _ _ _ h <;> aesop
  | ax | orR₁ | impR =>
    rw [←append_eq_of_mem (h mem_append_self)]
    simp [append_subset_iff] at h; cases h
    constructor <;> apply ih <;> (try apply append_subset_append) <;> aesop
  | orR₂ =>
    rw [←append_eq_of_mem (h mem_append_self)]
    simp [append_subset_iff] at h; cases h
    apply orR₂; apply ih <;> (try apply append_subset_append) <;> aesop
  | andR h₁ h₂ =>
    rw [←append_eq_of_mem (h mem_append_self)]
    simp [append_subset_iff] at h; cases h
    constructor
    · apply ih _ _ h₁ <;> (try apply append_subset_append) <;> aesop
    · apply ih _ _ h₂ <;> (try apply append_subset_append) <;> aesop
  | falseL | andL₁ | orL | impL =>
    constructor <;> apply ih <;> (try apply append_subset_append) <;> aesop
  | andL₂ =>
    apply andL₂; apply ih <;> (try apply append_subset_append) <;> aesop

theorem weakenR' : Γ ⊢[k] Δ → Γ ⊢[k] Δ,, p :=
  (weakenR · subset_append)

end HSequent

namespace Sequent

theorem hSequent : Γ ⊢ Δ → ∃ k, Γ ⊢[k] Δ := by
  intro h
  induction h with
  | ax | falseL => exists 0; aesop
  | andL₁ _ ih | andL₂ _ ih | orR₁ _ ih | orR₂ _ ih | impR _ ih =>
    rcases ih with ⟨k, ih⟩
    exists k + 1; aesop
  | andR _ _ ih₁ ih₂ | orL _ _ ih₁ ih₂ | impL _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨k₁, ih₁⟩
    rcases ih₂ with ⟨k₂, ih₂⟩
    exists max k₁ k₂ + 1
    constructor <;> apply HSequent.le (by assumption) <;> simp

theorem ax' : p ∈ Γ → p ∈ Δ → Γ ⊢ Δ := by
  intro h₁ h₂
  rw [←append_eq_of_mem h₁, ←append_eq_of_mem h₂]
  exact ax

theorem weakenL : Γ ⊢ Δ → Γ ⊆ Γ' → Γ' ⊢ Δ := by
  intro h₁ h
  rcases h₁.hSequent with ⟨k, h₁⟩
  apply HSequent.sequent
  exact HSequent.weakenL h₁ h

theorem weakenL' : Γ ⊢ Δ → Γ,, p ⊢ Δ := (weakenL · subset_append)

theorem weakenR : Γ ⊢ Δ → Δ ⊆ Δ' → Γ ⊢ Δ' := by
  intro h₁ h
  rcases h₁.hSequent with ⟨k, h₁⟩
  apply HSequent.sequent
  exact HSequent.weakenR h₁ h

theorem weakenR' : Γ ⊢ Δ → Γ ⊢ Δ,, p := (weakenR · subset_append)

theorem negL : Γ ⊢ Δ,, p → Γ,, ~ p ⊢ Δ := (impL · falseL)

theorem negR : Γ,, p ⊢ Δ → Γ ⊢ Δ,, ~ p := (impR $ weakenR' ·)

theorem trueR : Γ ⊢ Δ,, ⊤ := negR falseL

theorem double_neg : Γ,, p ⊢ Δ,, ~ ~ p := impR (negL ax)

theorem excluded_middle : Γ ⊢ Δ,, p ⋁ ~ p := by
  rw [←append_contraction]
  apply orR₁
  rw [append_exchange]
  apply orR₂
  apply negR
  exact ax

theorem double_neg_inv : Γ,, ~ ~ p ⊢ Δ,, p := by
  apply impL
  · apply impR; rw [append_exchange]; exact ax
  · exact falseL

theorem peirce : Γ ⊢ Δ,, ((p ⇒ q) ⇒ p) ⇒ p := by
  apply impR
  apply impL
  · apply impR
    rw [append_exchange]
    exact ax
  · exact ax

theorem consistency : ∅ ⊬ (∅ : Context α) := by
  suffices h : ∀ {Γ Δ : Context α}, Γ = ∅ → Δ = ∅ → Γ ⊬ Δ by
    apply h <;> rfl
  intros Γ Δ h₁ h₂ h
  cases h <;> (try exact append_ne_empty h₁) <;> exact append_ne_empty h₂

attribute [simp] Nat.add_succ Nat.succ_add Nat.lt_succ

theorem cut : Γ ⊢ Δ,, p → Γ,, p ⊢ Δ → Γ ⊢ Δ := by
  intro h₁ h₂
  induction' h : p.size using Nat.strongRecOn with _ ih₁ generalizing Γ Δ p; subst h
  apply hSequent at h₁; rcases h₁ with ⟨k₁, h₁⟩
  apply hSequent at h₂; rcases h₂ with ⟨k₂, h₂⟩
  induction' h : (k₁ + k₂) using Nat.strongRecOn with _ ih₂ generalizing Γ Δ k₁ k₂; subst h
  generalize h₃ : (Δ,, p) = Δ' at h₁
  generalize h₄ : (Γ,, p) = Γ' at h₂
  have h₁' := h₁
  cases h₁' with simp at *
  | succ h₁' => subst h₃ h₄; exact ih₂ _ (by rfl) _ h₁' _ h₂ rfl
  | ax =>
    subst h₄
    rcases append_eq_append h₃ with h₃' | ⟨_, h₃''⟩
    · subst h₃'; rw [append_contraction] at h₂; exact h₂.sequent
    · rw [←append_eq_of_mem h₃'']; exact ax
  | falseL => exact falseL
  | andL₁ | orL =>
    subst h₃ h₄; rw [←append_contraction]
    constructor <;> apply ih₂ _ (by rfl) _ _ _ _ rfl
      <;> rw [append_exchange] <;> apply HSequent.weakenL' <;> assumption
  | andL₂ =>
    subst h₃ h₄; rw [←append_contraction]
    apply andL₂; apply ih₂ _ (by rfl) _ _ _ _ rfl
     <;> rw [append_exchange] <;> apply HSequent.weakenL' <;> assumption
  | impL =>
    subst h₃ h₄; rw [←append_contraction]
    apply impL
    · apply ih₂ _ (by rfl) _ _ _ _ rfl
      · rw [append_exchange]; apply HSequent.weakenL'; assumption
      · apply HSequent.weakenR'; assumption
    · apply ih₂ _ (by rfl) _ _ _ _ rfl
        <;> rw [append_exchange] <;> apply HSequent.weakenL' <;> assumption
  | andR h₁' h₁'' | orR₁ h₁' | orR₂ h₁' | impR h₁' =>
    rcases append_eq_append h₃ with h₃' | ⟨h₃', h₃''⟩
    · subst h₃'
      have h₂' := h₂
      cases h₂' with simp at *
      | succ h₂' => subst h₄; rw [←h₃] at h₁; apply ih₂ _ _ _ h₁ _ h₂' rfl; simp
      | ax =>
        rcases (append_eq_append h₄) with h₄' | ⟨h₄', h₄''⟩
        · subst h₄'; rw [←h₃, append_contraction] at h₁; exact h₁.sequent
        · rw [←append_eq_of_mem h₄'']; exact ax
      | andR | orR₁ =>
        subst h₄
        rw [←append_contraction]
        constructor <;> (
          apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
          · rw [append_exchange, h₃]; exact HSequent.weakenR' h₁
          · rw [append_exchange]; apply HSequent.weakenR'; assumption)
      | orR₂ =>
        subst h₄
        rw [←append_contraction]
        apply orR₂; apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
        · rw [append_exchange, h₃]; exact HSequent.weakenR' h₁
        · rw [append_exchange]; apply HSequent.weakenR'; assumption
      | impR =>
        subst h₄
        rw [←append_contraction]
        apply impR; apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
        · rw [append_exchange, h₃]; apply HSequent.weakenL'; exact HSequent.weakenR' h₁
        · rw [append_exchange (a := _ ⇒ _), append_exchange (s := Γ)]
          apply HSequent.weakenR'; assumption
      | falseL =>
        rcases (append_eq_append h₄) with h₄' | ⟨h₄', h₄''⟩
        · injection h₄'
        · rw [←append_eq_of_mem h₄'']; exact falseL
      | andL₁ h₂' =>
        rcases (append_eq_append h₄) with h₄' | ⟨h₄', h₄''⟩
        · injection h₄'
          all_goals
            subst_vars
            apply ih₁ _ (Nat.le_add_right _ _) _ _ rfl
            · apply ih₂ _ (by simp; rfl) _ _ (Nat.succ _) _ rfl
              · rw [append_exchange, h₃, append_exchange]; exact HSequent.weakenR' h₁'
              · rw [h₄]; exact HSequent.weakenR' h₂
            · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
              · rw [h₃]; exact HSequent.weakenL' h₁
              · rw [append_exchange, h₄, append_exchange]; exact HSequent.weakenL' h₂'
        · rw [←append_eq_of_mem h₄'']
          apply andL₁
          apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
          · rw [h₃]; exact HSequent.weakenL' h₁
          · rw [append_exchange, h₄, append_exchange]; exact HSequent.weakenL' h₂'
      | andL₂ h₂' =>
        rcases (append_eq_append h₄) with h₄' | ⟨h₄', h₄''⟩
        · injection h₄'
          all_goals
            subst_vars
            apply ih₁ _ (Nat.le_add_left _ _) _ _ rfl
            · apply ih₂ _ (by simp; rfl) _ _ (Nat.succ _) _ rfl
              · rw [append_exchange, h₃, append_exchange]; exact HSequent.weakenR' h₁''
              · rw [h₄]; exact HSequent.weakenR' h₂
            · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
              · rw [h₃]; exact HSequent.weakenL' h₁
              · rw [append_exchange, h₄, append_exchange]; exact HSequent.weakenL' h₂'
        · rw [←append_eq_of_mem h₄'']
          apply andL₂
          apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
          · rw [h₃]; exact HSequent.weakenL' h₁
          · rw [append_exchange, h₄, append_exchange]; exact HSequent.weakenL' h₂'
      | orL h₂' h₂'' =>
        rcases (append_eq_append h₄) with h₄' | ⟨h₄', h₄''⟩
        · injection h₄'
          all_goals
            subst_vars
            first
            | apply ih₁ _ (Nat.le_add_right _ _) _ _ rfl
              apply ih₂ _ (by simp; rfl) _ _ (Nat.succ _) _ rfl
              rw [append_exchange, h₃, append_exchange]; exact HSequent.weakenR' h₁'
            | apply ih₁ _ (Nat.le_add_left _ _) _ _ rfl
              apply ih₂ _ (by simp; rfl) _ _ (Nat.succ _) _ rfl
              rw [append_exchange, h₃, append_exchange]; exact HSequent.weakenR' h₁'
            · rw [h₄]; exact HSequent.weakenR' h₂
            · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
              · rw [h₃]; exact HSequent.weakenL' h₁
              · rw [append_exchange, h₄, append_exchange]
                apply HSequent.weakenL'
                assumption
        · rw [←append_eq_of_mem h₄'']
          apply orL <;> (
            apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
            · rw [h₃]; exact HSequent.weakenL' h₁
            · rw [append_exchange, h₄, append_exchange]
              apply HSequent.weakenL'
              assumption)
      | impL h₂' h₂'' =>
        rcases (append_eq_append h₄) with h₄' | ⟨h₄', h₄''⟩
        · injection h₄'
          all_goals
            subst_vars
            apply ih₁ _ (Nat.le_add_left _ _) _ _ rfl
            · apply ih₁ _ (Nat.le_add_right _ _) _ _ rfl
              · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
                · rw [append_exchange]; apply HSequent.weakenR'
                  rw [append_exchange, h₃]; exact HSequent.weakenR' h₁
                · rw [append_exchange, h₄]
                  apply HSequent.weakenL'
                  exact HSequent.weakenR' h₂'
              · apply ih₂ _ (by simp; rfl) _ _ (Nat.succ _) _ rfl
                · rw [append_exchange, h₃, append_exchange]; exact HSequent.weakenR' h₁'
                · rw [append_exchange, h₄]
                  apply HSequent.weakenL'
                  exact HSequent.weakenR' h₂
            · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
              · rw [h₃]; exact HSequent.weakenL' h₁
              · rw [append_exchange, h₄, append_exchange]; exact HSequent.weakenL' h₂''
        · rw [←append_eq_of_mem h₄'']
          apply impL
          · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
            · rw [append_exchange, h₃]; exact HSequent.weakenR' h₁
            · rw [h₄]; exact HSequent.weakenL' h₂'
          · apply ih₂ _ (by simp; rfl) (Nat.succ _) _ _ _ rfl
            · rw [h₃]; exact HSequent.weakenL' h₁
            · rw [append_exchange, h₄, append_exchange]; exact HSequent.weakenL' h₂''
    · subst h₄
      rw [←append_eq_of_mem h₃'']
      first
      | constructor <;> apply ih₂ _ (by rfl) _ _ _ (HSequent.weakenR' h₂) rfl
          <;> rw [append_exchange, h₃, append_exchange]
          <;> apply HSequent.weakenR' <;> assumption
      | apply orR₂ <;> apply ih₂ _ (by rfl) _ _ _ (HSequent.weakenR' h₂) rfl
          <;> rw [append_exchange, h₃, append_exchange]
          <;> apply HSequent.weakenR' <;> assumption
      | apply impR; apply ih₂ _ (by rfl) _ _ _ _ rfl
        · rw [append_exchange, h₃, append_exchange]
          apply HSequent.weakenR'; assumption
        · rw [append_exchange]; apply HSequent.weakenL'; apply HSequent.weakenR'; assumption

theorem andL' : Γ,, p,, q ⊢ Δ → Γ,, p ⋀ q ⊢ Δ := by
  intro h
  apply cut (andL₁ ax)
  rw [append_exchange]
  apply cut (andL₂ ax)
  rw [append_exchange]
  exact weakenL' h

theorem andL'_inv : Γ,, p ⋀ q ⊢ Δ → Γ,, p,, q ⊢ Δ := by
  intro h
  apply cut
  · exact andR (weakenL' ax) ax
  · rw [append_exchange]; apply weakenL'
    rw [append_exchange]; exact weakenL' h

theorem andL'_iff : Γ,, p ⋀ q ⊢ Δ ↔ Γ,, p,, q ⊢ Δ := ⟨andL'_inv, andL'⟩

theorem andR_inv : Γ ⊢ Δ,, p ⋀ q → Γ ⊢ Δ,, p ∧ Γ ⊢ Δ,, q := by
  intro h
  constructor <;> apply cut (by rw [append_exchange]; exact weakenR' h) <;> aesop

theorem andR_iff : Γ ⊢ Δ,, p ⋀ q ↔ Γ ⊢ Δ,, p ∧ Γ ⊢ Δ,, q := ⟨andR_inv, and_imp.mpr andR⟩

theorem orL_inv : Γ,, p ⋁ q ⊢ Δ → Γ,, p ⊢ Δ ∧ Γ,, q ⊢ Δ := by
  intro h
  constructor <;> apply cut _ (by rw [append_exchange]; exact weakenL' h) <;> aesop

theorem orL_iff : Γ,, p ⋁ q ⊢ Δ ↔ Γ,, p ⊢ Δ ∧ Γ,, q ⊢ Δ := ⟨orL_inv, and_imp.mpr orL⟩

theorem orR' : Γ ⊢ Δ,, p,, q → Γ ⊢ Δ,, p ⋁ q := by
  intro h
  apply cut _ (orR₁ ax)
  rw [append_exchange]
  apply cut _ (orR₂ ax)
  rw [append_exchange]
  exact weakenR' h

theorem orR'_inv : Γ ⊢ Δ,, p ⋁ q → Γ ⊢ Δ,, p,, q := by
  intro h
  apply cut
  · rw [append_exchange]; apply weakenR'
    rw [append_exchange]; exact weakenR' h
  · exact orL (weakenR' ax) ax

theorem orR'_iff : Γ ⊢ Δ,, p ⋁ q ↔ Γ ⊢ Δ,, p,, q := ⟨orR'_inv, orR'⟩

theorem impR_inv : Γ ⊢ Δ,, p ⇒ q → Γ,, p ⊢ Δ,, q := by
  intro h
  apply cut
  · rw [append_exchange]; apply weakenL'; exact weakenR' h
  · exact impL ax ax

theorem impR_iff : Γ ⊢ Δ,, p ⇒ q ↔ Γ,, p ⊢ Δ,, q := ⟨impR_inv, impR⟩

end Sequent

end Propositional.LK
