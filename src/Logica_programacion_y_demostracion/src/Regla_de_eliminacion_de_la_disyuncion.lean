import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (h : P ∨ Q)
  (h1 : P → R)
  (h2 : Q → R)
  : R :=
by
  cases' h with hP hQ
  . -- hP : P
    exact h1 hP
  . -- hQ : Q
    exact h2 hQ

-- 2ª demostración
example
  (h : P ∨ Q)
  (h1 : P → R)
  (h2 : Q → R)
  : R :=
  match h with
  | Or.inl h => h1 h
  | Or.inr h => h2 h

-- 3ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
  Or.elim h1 h2 h3
