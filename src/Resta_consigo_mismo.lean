-- Resta_consigo_mismo.lean
-- Si R es un anillo y a ∈ R, entonces a - a = 0
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a ∈ R, entonces
--     a - a = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    a - a = a + -a    [por definición de resta]
--          = 0         [por suma con opuesto]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
example : a - a = 0 :=
calc
  a - a = a + -a := by rw [sub_eq_add_neg a a]
      _ = 0      := by rw [add_neg_cancel]

-- 2ª demostración
example : a - a = 0 :=
sub_self a

-- 3ª demostración
example : a - a = 0 :=
by simp

-- Lemas usados
-- ============

-- #check (add_neg_cancel a : a + -a = 0)
-- #check (sub_eq_add_neg a b : a - b = a + -b)
-- #check (sub_self a : a - a = 0)
