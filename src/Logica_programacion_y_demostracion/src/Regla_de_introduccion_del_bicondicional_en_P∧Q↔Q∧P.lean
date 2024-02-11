-- Regla de introducción del bicondicional
-- =======================================

-- ----------------------------------------------------
-- Ej. 1. (p. 17) Demostrar
--    P ∧ Q ↔ Q ∧ P
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  ( assume h1 : P ∧ Q,
    have h2 : P,
      from and.elim_left h1,
    have h3 : Q,
      from and.elim_right h1,
    show Q ∧ P,
      from and.intro h3 h2)
  ( assume h4 : Q ∧ P,
    have h5 : Q,
      from and.elim_left h4,
    have h6 : P,
      from and.elim_right h4,
    show P ∧ Q,
      from and.intro h6 h5)

-- 2ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  ( assume h1 : P ∧ Q,
    have h2 : P,
      from h1.1,
    have h3 : Q,
      from h1.2,
    show Q ∧ P,
      from and.intro h3 h2)
  ( assume h4 : Q ∧ P,
    have h5 : Q,
      from h4.1,
    have h6 : P,
      from h4.2,
    show P ∧ Q,
      from and.intro h6 h5)

-- 3ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  ( assume h1 : P ∧ Q,
    have h2 : P := h1.1,
    have h3 : Q := h1.2,
    show Q ∧ P,
      from and.intro h3 h2)
  ( assume h4 : Q ∧ P,
    have h5 : Q := h4.1,
    have h6 : P := h4.2,
    show P ∧ Q,
      from and.intro h6 h5)

-- 4ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  ( assume h1 : P ∧ Q,
    show Q ∧ P,
      from and.intro h1.2 h1.1)
  ( assume h4 : Q ∧ P,
    show P ∧ Q,
      from and.intro h4.2 h4.1)

-- 5ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  ( assume h1 : P ∧ Q, and.intro h1.2 h1.1)
  ( assume h4 : Q ∧ P, and.intro h4.2 h4.1)

-- 6ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  ( assume h1 : P ∧ Q, ⟨h1.2, h1.1⟩)
  ( assume h4 : Q ∧ P, ⟨h4.2, h4.1⟩)

-- 7ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  (λ h, ⟨h.2, h.1⟩)
  (λ h, ⟨h.2, h.1⟩)

-- 8ª demostración
example : P ∧ Q ↔ Q ∧ P :=
iff.intro
  (λ ⟨hP, hQ⟩, ⟨hQ, hP⟩)
  (λ ⟨hQ, hP⟩, ⟨hP, hQ⟩)

-- 9ª demostración
lemma aux :
  P ∧ Q → Q ∧ P :=
λ h, ⟨h.2, h.1⟩

example : P ∧ Q ↔ Q ∧ P :=
iff.intro (aux P Q) (aux Q P)

-- 10ª demostración
example : P ∧ Q ↔ Q ∧ P :=
-- by library_search
and.comm

-- 11ª demostración
example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  { intro h1,
    cases h1 with h2 h3,
    split,
    { exact h3, },
    { exact h2, }},
  { intro h4,
    cases h4 with h5 h6,
    split,
    { exact h6, },
    { exact h5, }},
end

-- 12ª demostración
example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  { rintro ⟨h2, h3⟩,
    split,
    { exact h3, },
    { exact h2, }},
  { rintro ⟨h5, h6⟩,
    split,
    { exact h6, },
    { exact h5, }},
end

-- 13ª demostración
example : P ∧ Q ↔ Q ∧ P :=
begin
  constructor,
  { rintro ⟨h2, h3⟩,
    constructor,
    { exact h3, },
    { exact h2, }},
  { rintro ⟨h5, h6⟩,
    constructor,
    { exact h6, },
    { exact h5, }},
end

-- 14ª demostración
example : P ∧ Q ↔ Q ∧ P :=
-- by hint
by tauto

-- 15ª demostración
example : P ∧ Q ↔ Q ∧ P :=
by finish
