-- Eliminacion_de_la_doble_negacion.lean
-- ¬¬P → P.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    ¬¬P → P
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que
--    ¬¬P                                                            (1)
--
-- Por el principio del tercio excluso, se tiene
--    P ∨ ¬P
-- lo que da lugar a dos casos.
--
-- En el primer caso, se supone P que es lo que hay que demostrar.
--
-- En el primer caso, se supone ¬P que es una contradicción con (1).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  have h2 : P ∨ ¬ P := em P
  rcases h2 with h3 | h4
  . -- h3 : P
    exact h3
  . -- h4 : ¬P
    exfalso
    -- ⊢ False
    exact h1 h4

-- 2ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  rcases em P with h2 | h3
  . -- h2 : P
    exact h2
  . -- h3 : ¬P
    exact absurd h3 h1

-- 3ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  cases em P
  . -- h2 : P
    assumption
  . -- h3 : ¬P
    contradiction

-- 4ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h
  by_cases P
  . assumption
  . contradiction

-- 4ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  by_contra h
  -- h : ¬P
  -- ⊢ False
  exact h1 h

-- 5ª demostración
-- ===============

example : ¬¬P → P :=
by tauto
