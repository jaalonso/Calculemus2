import Mathlib.Tactic
variable (P Q R : Prop)
open Classical

-- 1ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
by
  constructor
  . -- ⊢ ¬¬P
    exact not_not_intro h1
  . -- ⊢ R
    exact (not_not.mp h2).2

-- 2ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
  ⟨not_not_intro h1, (not_not.mp h2).right⟩
