import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª regla de introducción
example
  (h : P)
  : P ∨ Q :=
Or.inl h

-- 2ª regla de introducción
example
  (h : Q)
  : P ∨ Q :=
Or.inr h
