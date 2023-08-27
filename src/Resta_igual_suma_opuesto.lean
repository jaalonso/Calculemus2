-- Resta_igual_suma_opuesto.lean
-- Si R es un anillo y a, b ∈ R, entonces a - b = a + -b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a, b ∈ R, entonces
--    a - b = a + -b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la definición de la resta.

-- Demostración en Lean4
-- =====================

import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

example : a - b = a + -b :=
-- by exact?
sub_eq_add_neg a b

-- Lemas usados
-- ============

-- #check (sub_eq_add_neg a b : a - b = a + -b)
