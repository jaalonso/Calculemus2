-- Introduccion_doble_negacion.lean
-- P → ¬¬P.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que P → ¬¬P.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos ¬P. Entonces, tenemos una contradicción con la hipótesis
-- (P).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
by
  intro h1
  -- h1 : ¬P
  -- ⊢ False
  exact (h1 h)

-- 2ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
fun h1 ↦ h1 h

-- 3ª demostración
-- ===============

example
  (h : P)
  : ¬¬P :=
not_not_intro h

-- 4ª demostración
-- ===============

example
  (h : P)
  : ¬ ¬ P :=
by tauto

-- Lemas usados
-- ============

-- #check (not_not_intro : P → ¬¬P)
