import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
by
  intros h2 h3
  -- h2 : P
  -- h3 : ¬Q
  -- ⊢ False
  apply h1 h3
  -- ⊢ P
  exact h2

-- 2ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
  fun h2 h3 ↦ (h1 h3) h2
