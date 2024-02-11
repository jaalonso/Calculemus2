import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
by
  intros h1 h2 h3
  -- h1 : Q → R
  -- h2 : ¬Q → ¬P
  -- h3 : P
  -- ⊢ R
  apply h1
  -- ⊢ Q
  apply not_not.mp
  -- ⊢ ¬¬Q
  apply mt h2
  -- ⊢ ¬¬P
  exact not_not_intro h3

-- 2ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
  fun h1 h2 h3 ↦ h1 (not_not.mp (mt h2 (not_not_intro h3)))
