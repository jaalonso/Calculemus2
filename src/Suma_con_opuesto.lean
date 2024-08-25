-- Suma_con_opuesto.lean
-- Si R es un anillo y a ∈ R, entonces a + -a = 0
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar en Lean4 que si R es un anillo, entonces
--    ∀ a : R, a + -a = 0
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a + -a = -a + a    [por la conmutativa de la suma]
--           = 0         [por el axioma de inverso por la izquierda]

-- Demostración con Lean4
-- ======================

import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

-- 1ª demostración
-- ===============

example : a + -a = 0 :=
calc a + -a = -a + a := by rw [add_comm]
          _ = 0      := by rw [neg_add_cancel]

-- 2ª demostración
-- ===============

example : a + -a = 0 :=
by
  rw [add_comm]
  rw [neg_add_cancel]

-- 3ª demostración
-- ===============

example : a + -a = 0 :=
by rw [add_comm, neg_add_cancel]

-- 4ª demostración
-- ===============

example : a + -a = 0 :=
by exact add_neg_cancel a

-- 5ª demostración
-- ===============

example : a + -a = 0 :=
  add_neg_cancel a

-- 6ª demostración
-- ===============

example : a + -a = 0 :=
by simp

-- Lemas usados
-- ============

-- variable (a b : R)
-- #check (add_comm a b : a + b = b + a)
-- #check (add_neg_cancel a : a + -a = 0)
-- #check (neg_add_cancel a : -a + a = 0)
