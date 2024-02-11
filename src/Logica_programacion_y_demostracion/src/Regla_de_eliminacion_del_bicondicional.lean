-- Reglas de eliminacion del condicional
-- =====================================

-- ----------------------------------------------------
-- Ej. 1. (p. 18) Demostrar
--     P ↔ Q, P ∨ Q ⊢ P ∧ Q
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
or.elim h2
  ( assume h3 : P,
    have h4 : P → Q,
      from iff.elim_left h1,
    have h5 : Q,
      from h4 h3,
    show P ∧ Q,
      from and.intro h3 h5 )
  ( assume h6 : Q,
    have h7 : Q → P,
      from iff.elim_right h1,
    have h8 : P,
      from h7 h6,
    show P ∧ Q,
      from and.intro h8 h6 )

-- 2ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
or.elim h2
  ( assume h3 : P,
    have h4 : P → Q := h1.1,
    have h5 : Q := h4 h3,
    show P ∧ Q, from ⟨h3, h5⟩ )
  ( assume h6 : Q,
    have h7 : Q → P := h1.2,
    have h8 : P := h7 h6,
    show P ∧ Q, from ⟨h8, h6⟩ )

-- 3ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
or.elim h2
  ( assume h3 : P,
    show P ∧ Q, from ⟨h3, (h1.1 h3)⟩ )
  ( assume h6 : Q,
    show P ∧ Q, from ⟨h1.2 h6, h6⟩ )

-- 4ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
or.elim h2
  (λh, ⟨h, (h1.1 h)⟩)
  (λh, ⟨h1.2 h, h⟩)

example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
h2.elim
  (λh, ⟨h, (h1.1 h)⟩)
  (λh, ⟨h1.2 h, h⟩)

-- 5ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
begin
  cases h2 with h3 h4,
  { split,
    { exact h3, },
    { apply h1.mp,
      exact h3, }},
  { split,
    { apply h1.mpr,
      exact h4, },
    { exact h4, }},
end

-- 6ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
begin
  cases h2 with h3 h4,
  { split,
    { exact h3, },
    { rw ← h1,
      exact h3, }},
  { split,
    { rw h1,
      exact h4, },
    { exact h4, }},
end

-- 7ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
begin
  cases h2 with h3 h4,
  { split,
    { exact h3, },
    { rwa ← h1, }},
  { split,
    { rwa h1, },
    { exact h4, }},
end

-- 8ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
-- by hint
by tauto

-- 9ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
by finish

--10ª demostración
example
  (h1 : P ↔ Q)
  (h2 : P ∨ Q)
  : P ∧ Q :=
begin
  simp [h1] at h2 |-,
  assumption,
end
