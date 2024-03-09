import Mathlib.Order.BoundedOrder
import SequentCalculus.Finset

namespace Propositional

inductive Formula (α : Type u) where
| atom : α → Formula α
| false : Formula α
| and : Formula α → Formula α → Formula α
| or : Formula α → Formula α → Formula α
| imp : Formula α → Formula α → Formula α

instance : Bot (Formula α) := ⟨Formula.false⟩
infixr:70 (priority := high) " ⇒ " => Formula.imp
abbrev Formula.neg (p : Formula α) := p ⇒ ⊥
prefix:73 "~ " => Formula.neg
instance : Top (Formula α) := ⟨~ ⊥⟩
infix:71 " ⋁ " => Formula.or
infix:72 " ⋀ " => Formula.and

variable {α : Type u} [DecidableEq α]

instance Formula.decEq : DecidableEq (Formula α) := by
  intro p q
  cases p <;> cases q
  case atom.atom a b =>
    by_cases h : a = b
    · apply isTrue; rw [h]
    · apply isFalse; intro h'; injection h'; contradiction
  case false.false =>
    exact isTrue rfl
  case and.and p q p' q' | or.or p q p' q' | imp.imp p q p' q' =>
    cases decEq p p' with
    | isTrue h =>
      cases decEq q q' with
      | isTrue h' => apply isTrue; rw [h]; rw [h']
      | isFalse h' => apply isFalse; intro h''; injection h''; contradiction
    | isFalse h => apply isFalse; intro h'; injection h'; contradiction
  all_goals
    apply isFalse; intro h; injection h

@[simp] def Formula.size : Formula α → ℕ
| atom _ | ⊥ => 0
| p ⋀ q | p ⋁ q | p ⇒ q => p.size + q.size + 1

abbrev Context (α : Type u) := Finset (Formula α)

end Propositional
