import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
example : P → P :=
by
  intro h
  -- h : P
  -- ⊢ P
  exact h

-- 2ª demostración
example : P → P :=
fun h ↦ h

-- 3ª demostración
example : P → P :=
id
