import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
by
  intro h4
  -- h4 : Q
  -- ⊢ False
  apply h3
  -- ⊢ R
  apply (h1 h2)
  -- ⊢ Q
  exact h4

-- 2ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
  fun h4 ↦ h3 ((h1 h2) h4)
