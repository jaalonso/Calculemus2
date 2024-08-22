-- Opuesto_se_cancela_con_la_suma_por_la_derecha.lean
-- Si R es un anillo y a, b ∈ R, entonces (a + b) + -b = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar en Lean4 que si R es un anillo, entonces
--    ∀ a, b : R, (a + b) + -b = a
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    (a + b) + -b = a + (b + -b)    [por la asociativa]
--               _ = a + 0           [por suma con opuesto]
--               _ = a               [por suma con cero]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

-- 1ª demostración
example : (a + b) + -b = a :=
calc
  (a + b) + -b = a + (b + -b) := by rw [add_assoc]
             _ = a + 0        := by rw [add_neg_cancel]
             _ = a            := by rw [add_zero]

-- 2ª demostración
example : (a + b) + -b = a :=
by
  rw [add_assoc]
  rw [add_neg_cancel]
  rw [add_zero]

-- 3ª demostración
example : (a + b) + -b = a :=
by rw [add_assoc, add_neg_cancel, add_zero]

-- 4ª demostración
example : (a + b) + -b = a :=
  add_neg_cancel_right a b

-- 5ª demostración
example : (a + b) + -b = a :=
  add_neg_cancel_right _ _

-- 6ª demostración
example : (a + b) + -b = a :=
by simp

-- Lemas usados
-- ============

-- variable (c : R)
-- #check (add_assoc a b c : (a + b) + c = a + (b + c))
-- #check (add_neg_cancel a : a + -a = 0)
-- #check (add_neg_cancel_right a b : (a + b) + -b = a)
-- #check (add_zero a :  a + 0 = a)
