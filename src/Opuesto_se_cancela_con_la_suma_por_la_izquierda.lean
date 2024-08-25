-- Opuesto_se_cancela_con_la_suma_por_la_izquierda.lean
-- Si R es un anillo y a, b ∈ R, entonces -a + (a + b) = b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar en Lean4 que si R es un anillo, entonces
--    ∀ a, b : R, -a + (a + b) = b
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    -a + (a + b) = (-a + a) + b [por la asociativa]
--                 = 0 + b        [por inverso por la izquierda]
--                 = b            [por cero por la izquierda]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a b : R)

-- 1ª demostración
example : -a + (a + b) = b :=
calc -a + (a + b) = (-a + a) + b := by rw [← add_assoc]
                _ = 0 + b        := by rw [neg_add_cancel]
                _ = b            := by rw [zero_add]

-- 2ª demostración
example : -a + (a + b) = b :=
by
  rw [←add_assoc]
  rw [neg_add_cancel]
  rw [zero_add]

-- 3ª demostración
example : -a + (a + b) = b :=
by rw [←add_assoc, neg_add_cancel, zero_add]

-- 4ª demostración
example : -a + (a + b) = b :=
by exact neg_add_cancel_left a b

-- 5ª demostración
example : -a + (a + b) = b :=
  neg_add_cancel_left a b

-- 6ª demostración
example : -a + (a + b) = b :=
by simp

-- Lemas usados
-- ============

-- variable (c : R)
-- #check (add_assoc a b c : (a + b) + c = a + (b + c))
-- #check (neg_add_cancel a : -a + a = 0)
-- #check (neg_add_cancel_left a b : -a + (a + b) = b)
-- #check (zero_add a :  0 + a = a)
