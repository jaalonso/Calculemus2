import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
by
  have h4 : Q     := h2 h1
  have h5 : Q → R := h3 h1
  show R
  exact h5 h4

-- 2ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
(h3 h1) (h2 h1)
