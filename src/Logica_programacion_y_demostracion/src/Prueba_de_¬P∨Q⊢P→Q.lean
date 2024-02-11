import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
example
  (h : ¬P ∨ Q)
  : P → Q :=
by
  intro h1
  -- h1 : P
  -- ⊢ Q
  apply Or.elim h
  . -- ⊢ ¬P → Q
    intro h2
    -- h2 : ¬P
    -- ⊢ Q
    apply False.elim
    -- False
    exact h2 h1
  . -- ⊢ Q → Q
    exact id

-- 2ª demostración
example
  (h : ¬P ∨ Q)
  : P → Q :=
  fun h1 ↦ Or.elim h (fun h3 ↦ False.elim (h3 h1)) id
