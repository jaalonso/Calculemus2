import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (h : P ∧ Q)
  : P ∨ R :=
by
  left
  -- ⊢ P
  exact h.1

-- 2ª demostración
example
  (h : P ∧ Q)
  : P ∨ R :=
  Or.inl h.1

-- 3ª demostración
example :
  P ∧ Q → P ∨ R :=
by
  rintro ⟨h1, -⟩
  -- h1 : P
  -- ⊢ P ∨ R
  exact Or.inl h1

-- 4ª demostración
example :
  P ∧ Q → P ∨ R :=
  fun ⟨h1, _⟩ ↦ Or.inl h1
