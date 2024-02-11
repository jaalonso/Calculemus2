import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example : P ∧ Q → Q ∧ P :=
by
  intro h
  -- h : P ∧ Q
  -- ⊢ Q ∧ P
  exact ⟨h.2, h.1⟩

-- 2ª demostración
example : P ∧ Q → Q ∧ P :=
  fun h ↦ ⟨h.2, h.1⟩
