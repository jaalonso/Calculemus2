-- Implicacion_mediante_disyuncion_y_negacion.lean
-- (P → Q) ↔ ¬P ∨ Q
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (P → Q) ↔ ¬P ∨ Q
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Demostraremos cada una de las implicaciones.
--
-- (==>) Supongamos que P → Q. Distinguimos dos subcasos según el valor de
-- P.
--
-- Primer subcaso: suponemos P. Entonces. tenemos Q (por P → Q) y. por
-- tanto, ¬P ∨ Q.
--
-- Segundo subcaso: suponemos ¬P. Entonces. tenemos ¬P ∨ Q.
--
-- (<==) Supongamos que ¬P ∨ Q y P y tenemos que demostrar
-- Q. Distinguimos dos subcasos según ¬P ∨ Q.
--
-- Primer subcaso: Suponemos ¬P. Entonces tenemos una contradicción con
-- P.
--
-- Segundo subcaso: Suponemos Q, que es lo que tenemos que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
-- ===============

example
  : (P → Q) ↔ ¬P ∨ Q :=
by
  constructor
  . -- ⊢ (P → Q) → ¬P ∨ Q
    intro h1
    -- h1 : P → Q
    -- ⊢ ¬P ∨ Q
    by_cases h2 : P
    . -- h2 : P
      right
      -- ⊢ Q
      apply h1
      -- ⊢ P
      exact h2
    . -- h2 : ¬P
      left
      -- ⊢ ¬P
      exact h2
  . -- ⊢ ¬P ∨ Q → P → Q
    intros h3 h4
    -- h3 : ¬P ∨ Q
    -- h4 : P
    -- ⊢ Q
    rcases h3 with h3a | h3b
    . -- h : ¬P
      exact absurd h4 h3a
    . -- h : Q
      exact h3b

-- 2ª demostración
-- ===============

example
  : (P → Q) ↔ ¬P ∨ Q :=
by
  constructor
  . -- ⊢ (P → Q) → ¬P ∨ Q
    intro h1
    -- h1 : P → Q
    -- ⊢ ¬P ∨ Q
    by_cases h2: P
    . -- h2 : P
      right
      -- ⊢ Q
      exact h1 h2
    . -- h2 : ¬P
      left
      -- ⊢ ¬P
      exact h2
  . -- ⊢ ¬P ∨ Q → P → Q
    intros h3 h4
    -- h3 : ¬P ∨ Q
    -- h4 : P
    -- ⊢ Q
    cases h3
    . -- h : ¬P
      contradiction
    . -- h : Q
      assumption

-- 3ª demostración
-- ===============

example
  (P Q : Prop)
  : (P → Q) ↔ ¬P ∨ Q :=
imp_iff_not_or

-- 4ª demostración
-- ===============

example
  (P Q : Prop)
  : (P → Q) ↔ ¬P ∨ Q :=
by tauto
