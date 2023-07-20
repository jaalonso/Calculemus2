-- Suma_con_cero.lean
-- Si R es un anillo y a ∈ R, entonces a + 0 = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-julio-2023
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
--    ∀ a : R, a + 0 = a
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a + 0 = 0 + a    [por la conmutativa de la suma]
--          = a        [por el axioma del cero por la izquierda]

import Mathlib.Algebra.Ring.Defs

variable {R : Type _} [Ring R]
variable (a : R)

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example : a + 0 = a :=
calc a + 0
     = 0 + a := by rw [add_comm]
   _ = a     := by rw [zero_add]

-- 2ª demostración
example : a + 0 = a :=
by
  rw [add_comm]
  rw [zero_add]

-- 3ª demostración
example : a + 0 = a :=
by rw [add_comm, zero_add]

-- 4ª demostración
example : a + 0 = a :=
by exact add_zero a

-- 5ª demostración
example : a + 0 = a :=
  add_zero a

-- 5ª demostración
example : a + 0 = a :=
by simp
