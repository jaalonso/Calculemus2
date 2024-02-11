import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (h : P ∨ Q)
  : Q ∨ P :=
by
  apply Or.elim h
  . -- ⊢ P → Q ∨ P
    exact Or.inr
  . -- ⊢ Q → Q ∨ P
    exact Or.inl

-- 2ª demostración
example
  (h : P ∨ Q)
  : Q ∨ P :=
  Or.elim h Or.inr Or.inl

-- 3ª demostración
example
  (h : P ∨ Q)
  : Q ∨ P :=
  match h with
  | Or.inl h => Or.inr h
  | Or.inr h => Or.inl h
