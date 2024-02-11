import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h : False)
  : Q :=
False.elim h

-- 2ª demostración
example
  (h : False)
  : Q :=
by cases h
