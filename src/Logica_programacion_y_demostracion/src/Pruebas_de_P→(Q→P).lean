import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example : P → (Q → P) :=
by
  intro h1
  -- h1 : P
  -- ⊢ Q → P
  intro _h2
  -- _h2 : Q
  -- ⊢ P
  exact h1

-- 2ª demostración

example : P → (Q → P) :=
by
  intros h1 _h2
  -- h1 : P
  -- _h2 : Q
  -- ⊢ P
  exact h1

-- 3ª demostración
example : P → (Q → P) :=
fun h1 _ ↦ h1
