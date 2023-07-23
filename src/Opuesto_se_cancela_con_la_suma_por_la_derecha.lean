-- Opuesto_se_cancela_con_la_suma_por_la_derecha.lean
-- Si R es un anillo y a, b ∈ R, entonces (a + b) + -b = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, se declara que R es un anillo mediante la expresión
--    variable {R : Type _} [Ring R]
-- Como consecuencia, se tiene los siguientes axiomas
--    add_assoc    : ∀ a b c : R, (a + b) + c = a + (b + c)
--    add_comm     : ∀ a b : R,   a + b = b + a
--    zero_add     : ∀ a : R,     0 + a = a
--    add_left_neg : ∀ a : R,     -a + a = 0
--    mul_assoc    : ∀ a b c : R, a * b * c = a * (b * c)
--    mul_one      : ∀ a : R,     a * 1 = a
--    one_mul      : ∀ a : R,     1 * a = a
--    mul_add      : ∀ a b c : R, a * (b + c) = a * b + a * c
--    add_mul      : ∀ a b c : R, (a + b) * c = a * c + b * c
--
-- Demostrar que si R es un anillo, entonces
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
             _ = a + 0        := by rw [add_right_neg]
             _ = a            := by rw [add_zero]

-- 2ª demostración
example : (a + b) + -b = a :=
by
  rw [add_assoc]
  rw [add_right_neg]
  rw [add_zero]

-- 3ª demostración
example : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- 4ª demostración
example : (a + b) + -b = a :=
  add_neg_cancel_right a b

-- 5ª demostración
example : (a + b) + -b = a :=
  add_neg_cancel_right _ _

-- 6ª demostración
example : (a + b) + -b = a :=
by simp
