import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h1: P)
  (h2: ¬P)
  : False :=
by
  apply h2
  -- ⊢ P
  exact h1

-- 2ª demostración
example
  (h1: P)
  (h2: ¬P)
  : False :=
h2 h1
