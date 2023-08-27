-- a(be)_eq_c(df).lean
-- Si ab = cd y e = f, entonces a(be) = c(df).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b, c, d, e y f son números reales tales que
--    a * b = c * d y
--    e = f,
-- entonces
--    a * (b * e) = c * (d * f)
-- ---------------------------------------------------------------------

-- Demostración en leguaje natural
-- ===============================

-- Por la siguiente cadena de igualdades
--    a(be)
--    = a(bf)    [por la segunda hipótesis]
--    = (ab)f    [por la asociativa]
--    = (cd)f    [por la primera hipótesis]
--    = c(df)    [por la asociativa]

-- Demostraciones en Lean4
-- =======================

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc
  a * (b * e)
    = a * (b * f) := by rw [h2]
  _ = (a * b) * f := by rw [←mul_assoc]
  _ = (c * d) * f := by rw [h1]
  _ = c * (d * f) := by rw [mul_assoc]

-- 2ª demostración
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  rw [h2]
  rw [←mul_assoc]
  rw [h1]
  rw [mul_assoc]

-- 3ª demostración
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  simp [*, ←mul_assoc]

-- Lemas usados
-- ============

-- #check (mul_assoc : ∀ (a b c : ℝ), (a * b) * c = a * (b * c))
