-- Producto_por_dos.lean
-- Si R es un anillo y a ∈ R, entonces 2a = a+a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a ∈ R, entonces
--    2 * a = a + a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    2·a = (1 + 1)·a    [por la definición de 2]
--        = 1·a + 1·a    [por la distributiva]
--        = a + a        [por producto con uno]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
example : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   := by rw [one_add_one_eq_two]
      _ = 1 * a + 1 * a := by rw [add_mul]
      _ = a + a         := by rw [one_mul]

-- 2ª demostración
example : 2 * a = a + a :=
by exact two_mul a

-- Lemas usados
-- ============

-- variable (b c : R)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (one_add_one_eq_two : (1 : R) + 1 = 2)
-- #check (one_mul a : 1 * a = a)
-- #check (two_mul a : 2 * a = a + a)
