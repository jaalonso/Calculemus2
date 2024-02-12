import Mathlib.Tactic
variable (P Q : Prop)
open Classical

-- 1ª demostración
example
  (h : P → Q)
  : ¬P ∨ Q :=
by
  apply Or.elim (Classical.em P)
  . -- P → ¬P ∨ Q
    intro h1
    -- h1 : P
    -- ⊢ ¬P ∨ Q
    right
    -- ⊢ Q
    exact h h1
  . -- ⊢ ¬P → ¬P ∨ Q
    intro h2
    -- h2 : ¬P
    -- ⊢ ¬P ∨ Q
    left
    -- ⊢ ¬P
    exact h2

-- 2ª demostración
example
  (h : P → Q)
  : ¬P ∨ Q :=
  Or.elim (Classical.em P) (fun h1 ↦ Or.inr (h h1)) (fun h2 ↦ Or.inl h2)

-- 3ª demostración
example
  (h : P → Q)
  : ¬P ∨ Q :=
  Or.elim (Classical.em P) (Or.inr ∘ h) Or.inl
