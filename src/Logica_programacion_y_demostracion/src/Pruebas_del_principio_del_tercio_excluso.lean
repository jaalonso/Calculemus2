import Mathlib.Tactic
variable (F : Prop)
open Classical

-- 1ª demostración
example : F ∨ ¬F :=
by
  by_contra h1
  -- h1 : ¬(F ∨ ¬F)
  -- ⊢ False
  apply h1
  -- ⊢ F ∨ ¬F
  left
  -- ⊢ F
  by_contra h2
  apply h1
  -- ⊢ F ∨ ¬F
  right
  -- ⊢ ¬F
  exact h2

-- 2ª demostración
example : F ∨ ¬F :=
  byContradiction (fun h1 ↦ h1 (Or.inl (byContradiction (fun h2 ↦ h1 (Or.inr h2)))))
