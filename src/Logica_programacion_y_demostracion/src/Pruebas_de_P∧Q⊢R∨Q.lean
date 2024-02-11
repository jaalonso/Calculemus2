import Mathlib.Tactic
variable (P Q R : Prop)

-- ----------------------------------------------------
-- Ej. 4. Demostrar
--    P ∧ Q ⊢ R ∨ Q
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : P ∧ Q)
  : R ∨ Q :=
by
  right
  -- ⊢ Q
  exact h.2

-- 2ª demostración
example
  (h : P ∧ Q)
  : R ∨ Q :=
  Or.inr h.2

-- 3ª demostración
example :
  P ∧ Q → R ∨ Q :=
by
  rintro ⟨-, h2⟩
  -- h2 : Q
  -- ⊢ R ∨ Q
  exact Or.inr h2

-- 4ª demostración
example :
  P ∧ Q → R ∨ Q :=
  fun ⟨_, h2⟩ ↦ Or.inr h2
