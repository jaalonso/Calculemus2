import Mathlib.Tactic
variable (P : Prop)
open Classical

-- 1ª demostración
example
  (h : ¬¬P)
  : P :=
by
  by_contra h1
  -- h1 : ¬P
  -- ⊢ False
  exact h h1

-- 2ª demostración
example
  (h : ¬¬P)
  : P :=
  byContradiction (fun h1 => h h1)
