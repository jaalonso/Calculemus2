import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
example
  (h1 : P)
  : ¬¬P :=
by
  intro h2
  -- h2 : ¬P
  -- ⊢ False
  exact h2 h1

-- 2ª demostración
example
  (h1 : P)
  : ¬¬P :=
  fun h2 ↦ h2 h1
