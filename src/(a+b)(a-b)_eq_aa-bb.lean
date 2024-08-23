-- (a+b)(a-b)_eq_aa-bb.lean
-- (a+b)(a-b) = a^2-b^2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a y b son números reales, entonces
--    (a + b) * (a - b) = a^2 - b^2
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    (a + b)(a - b)
--    = a(a - b) + b(a - b)            [por la distributiva]
--    = (aa - ab) + b(a - b)           [por la distributiva]
--    = (a^2 - ab) + b(a - b)          [por def. de cuadrado]
--    = (a^2 - ab) + (ba - bb)         [por la distributiva]
--    = (a^2 - ab) + (ba - b^2)        [por def. de cuadrado]
--    = (a^2 + -(ab)) + (ba - b^2)     [por def. de resta]
--    = a^2 + (-(ab) + (ba - b^2))     [por la asociativa]
--    = a^2 + (-(ab) + (ba + -b^2))    [por def. de resta]
--    = a^2 + ((-(ab) + ba) + -b^2)    [por la asociativa]
--    = a^2 + ((-(ab) + ab) + -b^2)    [por la conmutativa]
--    = a^2 + (0 + -b^2)               [por def. de opuesto]
--    = (a^2 + 0) + -b^2               [por asociativa]
--    = a^2 + -b^2                     [por def. de cero]
--    = a^2 - b^2                      [por def. de resta]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

-- 1ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by rw [add_mul]
  _ = (a * a - a * b) + b * (a - b)     := by rw [mul_sub]
  _ = (a^2 - a * b) + b * (a - b)       := by rw [← pow_two]
  _ = (a^2 - a * b) + (b * a - b * b)   := by rw [mul_sub]
  _ = (a^2 - a * b) + (b * a - b^2)     := by rw [← pow_two]
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by rw [add_assoc]
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by rw [← add_assoc
                                              (-(a * b)) (b * a) (-b^2)]
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by rw [mul_comm]
  _ = a^2 + (0 + -b^2)                  := by rw [neg_add_cancel (a * b)]
  _ = (a^2 + 0) + -b^2                  := by rw [← add_assoc]
  _ = a^2 + -b^2                        := by rw [add_zero]
  _ = a^2 - b^2                         := by linarith

-- 2ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by ring
  _ = (a * a - a * b) + b * (a - b)     := by ring
  _ = (a^2 - a * b) + b * (a - b)       := by ring
  _ = (a^2 - a * b) + (b * a - b * b)   := by ring
  _ = (a^2 - a * b) + (b * a - b^2)     := by ring
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by ring
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by ring
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by ring
  _ = a^2 + (0 + -b^2)                  := by ring
  _ = (a^2 + 0) + -b^2                  := by ring
  _ = a^2 + -b^2                        := by ring
  _ = a^2 - b^2                         := by ring

-- 3ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

-- 4ª demostración
-- ===============

-- El lema anterior es
lemma aux : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- La demostración es
example : (a + b) * (a - b) = a^2 - b^2 :=
by
  rw [sub_eq_add_neg]
  rw [aux]
  rw [mul_neg]
  rw [add_assoc (a * a)]
  rw [mul_comm b a]
  rw [neg_add_cancel]
  rw [add_zero]
  rw [← pow_two]
  rw [mul_neg]
  rw [← pow_two]
  rw [← sub_eq_add_neg]

-- Lemas usados
-- ============

-- #check (add_assoc : ∀ (a b c : ℝ), (a + b) + c = a + (b + c))
-- #check (add_zero : ∀ (a : ℝ), a + 0 = a)
-- #check (add_mul : ∀ (a b c : ℝ), (a + b) * c = a * c + b * c)
-- #check (mul_comm : ∀ (a b : ℝ), a * b = b * a)
-- #check (mul_neg : ∀ (a b : ℝ), a * -b = -(a * b))
-- #check (mul_sub : ∀ (a b c : ℝ), a * (b - c) = a * b - a * c)
-- #check (neg_add_cancel : ∀ (a : ℝ), -a + a = 0)
-- #check (pow_two : ∀ (a : ℝ), a ^ 2 = a * a)
-- #check (sub_eq_add_neg : ∀ (a b : ℝ), a - b = a + -b)
