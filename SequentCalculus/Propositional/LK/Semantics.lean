import SequentCalculus.Propositional.LK.Sequent

namespace Propositional.LK

universe u v

variable {α : Type u} [DecidableEq α]

def Assignment (α) := α → Prop

open Formula in
def Assignment.eval : Assignment α → Formula α → Prop
| ρ, atom a => ρ a
| _, ⊥ => False
| ρ, p ⋀ q => ρ.eval p ∧ ρ.eval q
| ρ, p ⋁ q => ρ.eval p ∨ ρ.eval q
| ρ, p ⇒ q => ρ.eval p → ρ.eval q
scoped infix:55 " ⊨ₐ " => Assignment.eval

def entails (Γ Δ : Context α) :=
  ∀ ρ, (∀ p ∈ Γ, ρ ⊨ₐ p) → ∃ p ∈ Δ, ρ ⊨ₐ p
scoped infix:55 " ⊨ " => entails

variable {Γ Δ : Context α}

theorem soundness : Γ ⊢ Δ → Γ ⊨ Δ := by
  intro h ρ h₁
  induction h with simp [Assignment.eval] at *
  | @impR _ p => by_cases (ρ ⊨ₐ p) <;> aesop
  | _ => aesop

end Propositional.LK
