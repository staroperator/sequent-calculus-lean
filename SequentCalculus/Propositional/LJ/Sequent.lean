import SequentCalculus.Propositional.Syntax

namespace Propositional.LJ

open Formula

variable {α : Type u} [DecidableEq α]

@[aesop unsafe]
inductive Sequent : Context α → Formula α → Prop where
| ax : Sequent (Γ,, p) p
| falseL : Sequent (Γ,, ⊥) p
| andL₁ : Sequent (Γ,, p) r → Sequent (Γ,, p ⋀ q) r
| andL₂ : Sequent (Γ,, q) r → Sequent (Γ,, p ⋀ q) r
| andR : Sequent Γ p → Sequent Γ q → Sequent Γ (p ⋀ q)
| orL : Sequent (Γ,, p) r → Sequent (Γ,, q) r → Sequent (Γ,, p ⋁ q) r
| orR₁ : Sequent Γ p → Sequent Γ (p ⋁ q)
| orR₂ : Sequent Γ q → Sequent Γ (p ⋁ q)
| impL : Sequent Γ p → Sequent (Γ,, q) r → Sequent (Γ,, p ⇒ q) r
| impR : Sequent (Γ,, p) q → Sequent Γ (p ⇒ q)
scoped infix:55 " ⊢ " => Sequent
scoped notation:55 Γ " ⊬ " p:55 => ¬ (Γ ⊢ p)

@[aesop unsafe]
inductive HSequent : Context α → Formula α → Nat → Prop where
| ax : HSequent (Γ,, p) p 0
| falseL : HSequent (Γ,, ⊥) p 0
| andL₁ : HSequent (Γ,, p) r k → HSequent (Γ,, p ⋀ q) r (k + 1)
| andL₂ : HSequent (Γ,, q) r k → HSequent (Γ,, p ⋀ q) r (k + 1)
| andR : HSequent Γ p k → HSequent Γ q k → HSequent Γ (p ⋀ q) (k + 1)
| orL : HSequent (Γ,, p) r k → HSequent (Γ,, q) r k → HSequent (Γ,, p ⋁ q) r (k + 1)
| orR₁ : HSequent Γ p k → HSequent Γ (p ⋁ q) (k + 1)
| orR₂ : HSequent Γ q k → HSequent Γ (p ⋁ q) (k + 1)
| impL : HSequent Γ p k → HSequent (Γ,, q) r k → HSequent (Γ,, p ⇒ q) r (k + 1)
| impR : HSequent (Γ,, p) q k → HSequent Γ (p ⇒ q) (k + 1)
| succ : HSequent Γ p k → HSequent Γ p (k + 1)
scoped notation:55 Γ " ⊢[" k "] " p:55 => HSequent Γ p k

variable {Γ Δ : Context α} {p q r : Formula α}

open Finset

namespace HSequent

theorem sequent : Γ ⊢[k] p → Γ ⊢ p := by
  intro h
  induction h <;> aesop

theorem le : Γ ⊢[k] p → k ≤ k' → Γ ⊢[k'] p := by
  intro h h₁
  induction h₁ <;> aesop

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

theorem weakenL' : Γ ⊢[k] p → Γ,, q ⊢[k] p :=
  (weakenL · subset_add)

end HSequent

namespace Sequent

theorem hSequent : Γ ⊢ p → ∃ k, Γ ⊢[k] p := by
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

theorem ax' : p ∈ Γ → Γ ⊢ p := by
  intro h
  rw [←add_eq_of_mem h]
  exact ax

theorem weakenL : Γ ⊢ p → Γ ⊆ Δ → Δ ⊢ p := by
  intro h₁ h
  rcases h₁.hSequent with ⟨k, h₁⟩
  apply HSequent.sequent
  exact HSequent.weakenL h₁ h

theorem weakenL' : Γ ⊢ p → Γ,, q ⊢ p := (weakenL · subset_add)

theorem negL : Γ ⊢ p → Γ,, ~ p ⊢ ⊥ := (impL · falseL)

theorem negR : Γ,, p ⊢ ⊥ → Γ ⊢ ~ p := impR

theorem trueR : Γ ⊢ ⊤ := negR falseL

theorem double_neg : Γ,, p ⊢ ~ ~ p := impR (negL ax)

theorem negOrL₁ : Γ,, ~ (p ⋁ q) ⊢ ~ p := by
  apply impR
  rw [add_exchange]
  apply negL
  exact orR₁ ax

theorem negOrL₂ : Γ,, ~ (p ⋁ q) ⊢ ~ q := by
  apply impR
  rw [add_exchange]
  apply negL
  exact orR₂ ax

theorem excluded_middle_irrefutable : Γ ⊢ ~ (p ⋀ ~ p) := by
  apply impR
  rw [←add_contraction]
  apply andL₁
  rw [add_exchange]
  apply andL₂
  apply impL <;> exact ax

theorem consistency : ∅ ⊬ (⊥ : Formula α) := by
  intro h
  generalize h₁ : (∅ : Context α) = Γ at h
  cases h <;> exact add_ne_empty (Eq.symm h₁)

theorem or_inv : ∅ ⊢ p ⋁ ~ p → ∅ ⊢ p ∨ ∅ ⊢ ~ p := by
  intro h
  generalize h₁ : (∅ : Context α) = Γ at h
  cases h <;> (try cases add_ne_empty (Eq.symm h₁)) <;> aesop

theorem no_excluded_middle :
  Nonempty α → ¬ (∀ (Γ : Context α) p, Γ ⊢ p ⋁ ~ p) := by
  intro ⟨a⟩ h
  replace h := h ∅ (atom a)
  apply or_inv at h
  rcases h with h | h
    <;> generalize h₁ : (∅ : Context α) = Γ at h
    <;> cases h <;> (try cases add_ne_empty (Eq.symm h₁))
  case impR h =>
    subst h₁
    generalize h₁ : (∅,, atom a) = Γ at h
    cases h <;> rcases (add_eq_add h₁) with h₂ | ⟨h₂, h₃⟩
      <;> (try injection h₂) <;> simp at h₃

attribute [simp] Nat.add_succ Nat.succ_add Nat.lt_succ

theorem cut : Γ ⊢ p → Γ,, p ⊢ q → Γ ⊢ q := by
  intro h₁ h₂
  induction' h : p.size using Nat.strongRecOn with _ ih₁ generalizing Γ p q; subst h
  apply hSequent at h₁; rcases h₁ with ⟨k₁, h₁⟩
  apply hSequent at h₂; rcases h₂ with ⟨k₂, h₂⟩
  induction' h : (k₁ + k₂) using Nat.strongRecOn with _ ih₂ generalizing Γ q k₁ k₂; subst h
  generalize h : (Γ,, p) = Δ at h₂
  have h₁' := h₁
  cases h₁' with simp at *
  | succ h₁' => subst h; exact ih₂ _ (by rfl) _ h₁' _ h₂ rfl
  | ax => subst h; rw [add_contraction] at h₂; exact h₂.sequent
  | falseL => exact falseL
  | andL₁ | orL =>
    subst h; rw [←add_contraction]
    constructor <;> apply ih₂ _ (by rfl) _ _ _ _ rfl
      <;> rw [add_exchange] <;> apply HSequent.weakenL' <;> assumption
  | andL₂ =>
    subst h; rw [←add_contraction]
    apply andL₂; apply ih₂ _ (by rfl) _ _ _ _ rfl
     <;> rw [add_exchange] <;> apply HSequent.weakenL' <;> assumption
  | impL =>
    subst h; rw [←add_contraction]
    apply impL
    · apply weakenL'; apply HSequent.sequent; assumption
    · apply ih₂ _ (by rfl) _ _ _ _ rfl
        <;> rw [add_exchange] <;> apply HSequent.weakenL' <;> assumption
  | andR h₁' h₁'' | orR₁ h₁' | orR₂ h₁' | impR h₁' =>
    have h₂' := h₂
    cases h₂' with simp at *
    | succ h₂' => subst h; exact ih₂ _ (by simp) _ h₁ _ h₂' rfl
    | ax =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · subst h'; exact h₁.sequent
      · exact ax' h''
    | andR | orR₁ =>
      subst h
      constructor <;> apply ih₂ _ (by simp; rfl) _ h₁ _ (by assumption) rfl
    | orR₂ h₂' =>
      subst h; apply orR₂; exact ih₂ _ (by simp) _ h₁ _ h₂' rfl
    | impR h₂' =>
      subst h
      apply impR
      apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
      rw [add_exchange]; exact h₂'
    | falseL =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
      · rw [←add_eq_of_mem h'']; exact falseL
    | andL₁ h₂' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply ih₁ _ (by simp) h₁'.sequent _ rfl
          apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
          rw [add_exchange, h, add_exchange]; exact HSequent.weakenL' h₂'
      · rw [←add_eq_of_mem h'']
        apply andL₁
        apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
        rw [add_exchange, h, add_exchange]; exact HSequent.weakenL' h₂'
    | andL₂ h₂' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply ih₁ _ (by simp) h₁''.sequent _ rfl
          apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
          rw [add_exchange, h, add_exchange]; exact HSequent.weakenL' h₂'
      · rw [←add_eq_of_mem h'']
        apply andL₂
        apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
        rw [add_exchange, h, add_exchange]; exact HSequent.weakenL' h₂'
    | orL h₂' h₂'' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply ih₁ _ (by simp) h₁'.sequent _ rfl
          apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
          rw [add_exchange, h, add_exchange]; apply HSequent.weakenL'; assumption
      · rw [←add_eq_of_mem h'']
        apply orL
          <;> apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
          <;> rw [add_exchange, h, add_exchange] <;> apply HSequent.weakenL'
          <;> assumption
    | impL h₂' h₂'' =>
      rcases (add_eq_add h) with h' | ⟨h', h''⟩
      · injection h'
        all_goals
          subst_vars
          apply ih₁ _ (Nat.le_add_left _ _) _ _ rfl
          · apply ih₁ _ (by simp) _ h₁'.sequent rfl
            apply ih₂ _ (by simp; rfl) _ h₁ _ _ rfl
            rw [h]; exact HSequent.weakenL' h₂'
          · apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
            rw [add_exchange, h, add_exchange]; exact HSequent.weakenL' h₂''
      · rw [←add_eq_of_mem h'']
        apply impL
        · apply ih₂ _ (by simp; rfl) _ h₁ _ _ rfl
          rw [h]; exact HSequent.weakenL' h₂'
        · apply ih₂ _ (by simp; rfl) _ (HSequent.weakenL' h₁) _ _ rfl
          rw [add_exchange, h, add_exchange]; exact HSequent.weakenL' h₂''

theorem andL' : Γ,, p,, q ⊢ r → Γ,, p ⋀ q ⊢ r := by
  intro h
  apply cut (andL₁ ax)
  rw [add_exchange]
  apply cut (andL₂ ax)
  rw [add_exchange]
  exact weakenL' h

theorem andL'_inv : Γ,, p ⋀ q ⊢ r → Γ,, p,, q ⊢ r := by
  intro h
  apply cut
  · exact andR (weakenL' ax) ax
  · rw [add_exchange]; apply weakenL'
    rw [add_exchange]; exact weakenL' h

theorem andL'_iff : Γ,, p ⋀ q ⊢ r ↔ Γ,, p,, q ⊢ r := ⟨andL'_inv, andL'⟩

theorem andR_inv : Γ ⊢ p ⋀ q → Γ ⊢ p ∧ Γ ⊢ q := by
  intro h
  constructor <;> apply cut h <;> aesop

theorem andR_iff : Γ ⊢ p ⋀ q ↔ Γ ⊢ p ∧ Γ ⊢ q := ⟨andR_inv, and_imp.mpr andR⟩

theorem orL_inv : Γ,, p ⋁ q ⊢ r → Γ,, p ⊢ r ∧ Γ,, q ⊢ r := by
  intro h
  constructor <;> apply cut _ (by rw [add_exchange]; exact weakenL' h) <;> aesop

theorem orL_iff : Γ,, p ⋁ q ⊢ r ↔ Γ,, p ⊢ r ∧ Γ,, q ⊢ r := ⟨orL_inv, and_imp.mpr orL⟩

theorem impR_inv : Γ ⊢ p ⇒ q → Γ,, p ⊢ q := by
  intro h
  apply cut (weakenL' h)
  exact impL ax ax

theorem impR_iff : Γ ⊢ p ⇒ q ↔ Γ,, p ⊢ q := ⟨impR_inv, impR⟩

theorem no_double_neg_inv :
  Nonempty α → ¬ (∀ (Γ : Context α) p, Γ,, ~ ~ p ⊢ p) := by
  intro h₁ h
  apply no_excluded_middle h₁
  intros Γ p
  apply cut _ (h Γ _)
  apply impR
  apply cut negOrL₂
  apply impL _ ax
  exact negOrL₁

end Sequent
