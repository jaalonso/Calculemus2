-- Uno_mas_uno_es_dos.lean
-- En los anillos, 1 + 1 = 2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los anillos,
--    1 + 1 = 2
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por cálculo.

-- Demostración con Lean4
-- ======================

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic
variable {R : Type _} [Ring R]

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example : 1 + 1 = (2 : R) :=
by norm_num

-- 2ª demostración
example : 1 + 1 = (2 : R) :=
one_add_one_eq_two

-- Lemas usados
-- ============

-- #check (one_add_one_eq_two : 1 + 1 = 2)
