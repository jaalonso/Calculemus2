import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
by
  intro h3
  -- h3 : P
  -- ⊢ False
  have h4 : Q  := h1 h3
  have h5 : ¬Q := h2 h3
  show False
  exact h5 h4

-- 2ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
  fun h3 ↦ (h2 h3) (h1 h3)
