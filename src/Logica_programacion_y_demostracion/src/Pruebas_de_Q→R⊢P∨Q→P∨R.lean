import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (h : Q → R)
  : P ∨ Q → P ∨ R :=
by
  intro h1
  -- h1 : P ∨ Q
  -- ⊢ P ∨ R
  apply Or.elim h1
  . -- ⊢ P → P ∨ R
    exact Or.inl
  . -- ⊢ Q → P ∨ R
    intro h2
    -- h2 : Q
    -- ⊢ P ∨ R
    apply Or.inr
    -- ⊢ R
    exact h h2

-- 2ª demostración
example
  (h : Q → R)
  : P ∨ Q → P ∨ R :=
by
  intro h1
  -- h1 : P ∨ Q
  -- ⊢ P ∨ R
  apply Or.elim h1
  . -- ⊢ P → P ∨ R
    exact Or.inl
  . exact (fun h2 ↦ Or.inr (h h2))

-- 3ª demostración
example
  (h : Q → R)
  : P ∨ Q → P ∨ R :=
by
  intro h1
  -- h1 : P ∨ Q
  -- ⊢ P ∨ R
  apply Or.elim h1
  . -- ⊢ P → P ∨ R
    exact Or.inl
  . exact Or.inr ∘ h

-- 4ª demostración
example
  (h : Q → R)
  : P ∨ Q → P ∨ R :=
  fun h1 ↦ Or.elim h1 Or.inl (Or.inr ∘ h)
