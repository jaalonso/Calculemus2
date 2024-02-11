import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
by
  intros h2 h3
  -- h2 : ¬Q
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
  : ¬Q → ¬P :=
  fun h2 h3 ↦ h2 (h1 h3)
