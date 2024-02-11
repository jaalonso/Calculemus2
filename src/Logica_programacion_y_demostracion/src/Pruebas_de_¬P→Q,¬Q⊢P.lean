import Mathlib.Tactic
variable (P Q : Prop)
open Classical

-- 1ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
by
  by_contra h3
  -- h3 : ¬P
  -- ⊢ False
  apply h2
  -- ⊢ Q
  exact h1 h3

-- 2ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
  by_contra (fun h3 ↦ h2 (h1 h3))

-- 3ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
  by_contra (h2 ∘ h1)
