-- Inecuaciones.lean
-- En ℝ, si 2a ≤ 3b, 1 ≤ a y c = 2, entonces c + a ≤ 5b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b y c son números reales tales que
--    2 * a ≤ 3 * b
--    1 ≤ a
--    c = 2
-- entonces
--    c + a ≤ 5 * b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de desigualdades
--    c + a = 2 + a      [por la hipótesis 3 (c = 2)]
--          ≤ 2·a + a    [por la hipótesis 2 (1 ≤ a)]
--          = 3·a
--          ≤ 9/2·b      [por la hipótesis 1 (2·a ≤ 3·b)]
--          ≤ 5·b

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

-- 1ª demostración
example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
calc
  c + a = 2 + a     := by rw [h3]
      _ ≤ 2 * a + a := by linarith only [h2]
      _ = 3 * a     := by linarith only []
      _ ≤ 9/2 * b   := by linarith only [h1]
      _ ≤ 5 * b     := by linarith

-- 2ª demostración
example
  (h1 : 2 * a ≤ 3 * b)
  (h2 : 1 ≤ a)
  (h3 : c = 2)
  : c + a ≤ 5 * b :=
by linarith
