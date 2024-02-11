import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h1 : P → Q)
  (h2 : P)
  : Q :=
by tauto

-- 2ª demostración
example
  (h1 : P → Q)
  (h2 : P)
  : Q :=
by
  apply h1
  -- ⊢ P
  exact h2

-- 3ª demostración
example
  (h1 : P → Q)
  (h2 : P)
  : Q :=
h1 h2
