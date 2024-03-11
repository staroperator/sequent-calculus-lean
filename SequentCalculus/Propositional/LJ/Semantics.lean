import SequentCalculus.Propositional.LJ.Sequent

namespace Propositional.LJ

universe u v

structure KripkeModel (α : Type u) where
  W : Type v
  [preorder : Preorder W]
  ρ : α → W → Prop
  persist : ∀ a w, ∀ u ≥ w, ρ a w → ρ a u

instance : CoeSort (KripkeModel α) Type* := ⟨KripkeModel.W⟩

variable {α : Type u} [DecidableEq α] {Γ : Context α}
  {W : KripkeModel α} {u w : W}

instance : Preorder W := W.preorder

open Formula

def KripkeModel.force : W → Formula α → Prop
| w, atom a => W.ρ a w
| _, ⊥ => False
| w, p ⋀ q => force w p ∧ force w q
| w, p ⋁ q => force w p ∨ force w q
| w, p ⇒ q => ∀ u ≥ w, force u p → force u q
scoped infix:50 " ⊩ " => KripkeModel.force

theorem KripkeModel.force_mono : u ≥ w → w ⊩ p → u ⊩ p := by
  intro h₁ h₂
  induction p with simp [force] at *
  | atom => apply W.persist <;> aesop
  | imp => intros v h₃ h₄; exact h₂ _ (le_trans h₁ h₃) h₄
  | _ => aesop

def entails (Γ : Context α) (p : Formula α) :=
  ∀ (W : KripkeModel.{u,v} α) (w : W), (∀ p ∈ Γ, w ⊩ p) → w ⊩ p
scoped infix:55 " ⊨ " => entails

example {a : α} : ¬ ∅ ⊨ atom a ⋁ ~ atom a := by
  intro h
  let W : KripkeModel α := {
    W := Bool
    ρ := λ _ w => w
    persist := by intros _ w u h₁ h₂; cases h₁ h₂; trivial
  }
  have h₁ := h W false (by intro p h; cases h)
  simp [KripkeModel.force] at h₁

theorem soundness : Γ ⊢ p → Γ ⊨ p := by
  intro h W w h₁
  induction h generalizing w with simp [KripkeModel.force] at *
  | impR _ ih =>
    intros u h₂ h₃
    apply ih _ h₃
    intro p h
    apply KripkeModel.force_mono h₂
    exact h₁ _ h
  | _ => aesop

end Propositional.LJ
