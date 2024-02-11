import Mathlib.Tactic
variable (P Q : Prop)
open Classical

-- 1ª demostración
example
  (h : P → Q)
  : ¬P ∨ Q :=
by
  by_cases h1 : P
  . -- h1 : P
    right
    -- ⊢ Q
    exact h h1
  . -- h1 : ¬P
    left
    -- ⊢ ¬P
    exact h1

-- 2ª demostración
example
  (h : P → Q)
  : ¬P ∨ Q :=
  Classical.by_cases (fun h1 ↦ Or.inr (h h1)) (fun h1 ↦ Or.inl h1)

-- 3ª demostración
example
  (h : P → Q)
  : ¬P ∨ Q :=
  Classical.by_cases (Or.inr ∘ h) Or.inl
