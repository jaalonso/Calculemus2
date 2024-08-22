-- Opuesto_del_opuesto.lean
-- Si R es un anillo y a ∈ R, entonces -(-a) = a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a ∈ R, entonces
--     -(-a) = a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia de las siguiente propiedades demostradas en
-- ejercicios anteriores:
--    ∀ a b ∈ R, a + b = 0 → -a = b
--    ∀ a ∈ R, -a + a = 0

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

variable {R : Type _} [Ring R]
variable {a : R}

-- 1ª demostración
example : -(-a) = a :=
by
  have h1 : -a + a = 0 := neg_add_cancel a
  show -(-a) = a
  exact neg_eq_of_add_eq_zero_right h1

-- 2ª demostración
example : -(-a) = a :=
by
  apply neg_eq_of_add_eq_zero_right
  rw [neg_add_cancel]

-- 3ª demostración
example : -(-a) = a :=
neg_neg a

-- 4ª demostración
example : -(-a) = a :=
by simp

-- Lemas usados
-- ============

-- variable (b : R)
-- #check (neg_add_cancel a : -a + a = 0)
-- #check (neg_eq_of_add_eq_zero_right : a + b = 0 → -a = b)
-- #check (neg_neg a : -(-a) = a)
