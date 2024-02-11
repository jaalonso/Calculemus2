import Mathlib.Tactic
variable (P Q R : Prop)

-- 1º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
by
  intro h
  -- h : P
  -- ⊢ R
  apply h2
  -- ⊢ Q
  apply h1
  -- ⊢ P
  exact h

-- 2º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
fun h ↦ h2 (h1 h)

-- 3º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
h2 ∘ h1
