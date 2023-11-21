-- Eliminacion_doble_negacion.lean
-- ¬¬P → P
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que ¬¬P → P.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por reducción al absurdo. Supongamos ¬P. Entonces, tenemos una
-- contradicción con la hipótesis (¬¬P).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
by
  by_contra h1
  -- h1 : ¬P
  -- ⊢ False
  exact (h h1)

-- 2ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
by_contra (fun h1 ↦ h h1)

-- 3ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
-- not_not.mp h
of_not_not h

-- 4ª demostración
-- ===============

example
  (h : ¬¬P)
  : P :=
by tauto

-- Lemas usados
-- ============

-- #check (of_not_not : ¬¬P → P)
