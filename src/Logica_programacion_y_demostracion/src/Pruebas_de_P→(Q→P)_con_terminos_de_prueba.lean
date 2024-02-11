-- Pruebas de P → (Q → P)
-- ======================

-- ----------------------------------------------------
-- Ej. 1. (p. 13) Demostrar
--    P → (Q → P)
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  ( assume h2 : Q,
    show P, from h1)

lemma ejemplo1 : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  ( assume h2 : Q,
    show P, from h1)

#print ejemplo1
-- Escribe
--    theorem ejemplo1 : ∀ (P Q : Prop), P → Q → P :=
--    λ (P Q : Prop) (h1 : P), show Q → P, from λ (h2 : Q), show P, from h1

-- 2ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  ( assume h2 : Q, h1)

-- 3ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  (λ h2, h1)

-- 4ª demostración
example : P → (Q → P) :=
assume (h1 : P), (λ h2, h1)

-- 5ª demostración
example : P → (Q → P) :=
λ h1, λ h2, h1

lemma ejemplo2 : P → (Q → P) :=
λ h1 h2, h1

#print ejemplo2
-- Escribe
--    theorem ejemplo2 : ∀ (P Q : Prop), P → Q → P :=
--    λ (P Q : Prop) (h1 : P) (h2 : Q), h1

-- 6ª demostración
example : P → (Q → P) :=
λ h1 h2, h1

-- 7ª demostración
example : P → (Q → P) :=
λ h _, h

-- 8ª demostración
example : P → (Q → P) :=
-- by library_search
imp_intro

-- 9ª demostración
example : P → (Q → P) :=
begin
  intro h1,
  intro h2,
  exact h1,
end

lemma ejemplo3 : P → (Q → P) :=
begin
  intro h1,
  intro h2,
  exact h1,
end

#print ejemplo3
-- Escribe
--    theorem ejemplo3 : ∀ (P Q : Prop), P → Q → P :=
--    λ (P Q : Prop) (h1 : P) (h2 : Q), h1

-- 10ª demostración
example : P → (Q → P) :=
begin
  intros h1 h2,
  exact h1,
end

-- 11ª demostración
example : P → (Q → P) :=
λ h1 h2, h1

-- 12ª demostración
example : P → (Q → P) :=
-- by hint
by tauto

lemma ejemplo4 : P → (Q → P) :=
by tauto

#print ejemplo4
-- Escribe
--    theorem ejemplo4 : ∀ (P Q : Prop), P → Q → P :=
--    λ (P Q : Prop) (a : P) (a_1 : Q), rfl.mpr a

-- 13ª demostración
example : P → (Q → P) :=
by finish

lemma ejemplo5 : P → (Q → P) :=
by finish

#print ejemplo5
-- Escribe
--    λ (P Q : Prop),
--      (id (eq.refl (P → Q → P))).mpr
--      (λ (a : P) (a_1 : Q), classical.by_contradiction (λ (a_2 : ¬P), absurd a a_2))
