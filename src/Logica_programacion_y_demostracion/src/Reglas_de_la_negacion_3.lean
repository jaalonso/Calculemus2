import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
example : ¬(P ∧ ¬P) :=
by
  intro h
  -- h : P ∧ ¬P
  -- ⊢ False
  exact h.2 h.1

-- 2ª demostración
example : ¬(P ∧ ¬P) :=
  fun h ↦ h.2 h.1

-- 3ª demostración
example : ¬(P ∧ ¬P) :=
by
  rintro ⟨h1, h2⟩
  -- h1 : P
  -- h2 : ¬P
  -- ⊢ False
  exact h2 h1

-- 4ª demostración
example : ¬(P ∧ ¬P) :=
  fun ⟨h1, h2⟩ ↦ h2 h1
