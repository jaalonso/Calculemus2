import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
by
  intro h3
  -- h3 : P
  -- ⊢ False
  apply h2
  -- ⊢ Q
  apply h1
  -- ⊢ P
  exact h3

-- 2ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
  fun h3 ↦ h2 (h1 h3)

-- 3ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
  h2 ∘ h1
