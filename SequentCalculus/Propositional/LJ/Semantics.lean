import SequentCalculus.Propositional.LJ.Sequent

namespace Propositional.LJ

universe u v

@[class] structure KripkeModel (W : Type v) [Preorder W] (α : Type u) where
  ρ : W → α → Prop
  persist : ∀ w a, ∀ u ≥ w, ρ w a → ρ u a

variable {α : Type u} [DecidableEq α] {Γ : Context α} {p : Formula α}
  {W : Type v} [Preorder W] [M : KripkeModel W α] {u w : W}

open Formula

def KripkeModel.force : W → Formula α → Prop
| w, atom a => M.ρ w a
| _, ⊥ => False
| w, p ⋀ q => force w p ∧ force w q
| w, p ⋁ q => force w p ∨ force w q
| w, p ⇒ q => ∀ u ≥ w, force u p → force u q
scoped infix:50 " ⊩ " => KripkeModel.force

theorem KripkeModel.force_mono : u ≥ w → w ⊩ p → u ⊩ p := by
  intro h₁ h₂
  induction p with simp [force] at *
  | atom => apply M.persist <;> aesop
  | imp => intros v h₃ h₄; exact h₂ _ (le_trans h₁ h₃) h₄
  | _ => aesop

def entails (Γ : Context α) (p : Formula α) :=
  ∀ (W : Type v) [Preorder W] [KripkeModel W α] (w : W), (∀ p ∈ Γ, w ⊩ p) → w ⊩ p
scoped infix:55 " ⊨ " => entails

example {a : α} : ¬ ∅ ⊨ atom a ⋁ ~ atom a := by
  intro h
  letI : KripkeModel Bool α := {
    ρ := λ w _ => w
    persist := by intros _ _ u h₁ h₂; cases h₁ h₂; trivial
  }
  have h₁ := h Bool false (by intro p h; cases h)
  simp [KripkeModel.force] at h₁

theorem soundness : Γ ⊢ p → Γ ⊨ p := by
  intro h W _ _ w h₁
  induction h generalizing w with simp [KripkeModel.force] at *
  | impR _ ih =>
    intros u h₂ h₃
    apply ih _ h₃
    intro p h
    apply KripkeModel.force_mono h₂
    exact h₁ _ h
  | _ => aesop

end Propositional.LJ
