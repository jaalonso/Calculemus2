-- a(bc)_eq_b(ac).lean
-- ∀ a b c ∈ ℝ, a(bc) = b(ac)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-julio-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que los números reales tienen la siguiente propiedad
--    a * (b * c) = b * (a * c)
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades:
--    a(bc)
--    = (ab)c    [por la asociativa]
--    = (ba)c    [por la conmutativa]
--    = b(ac)    [por la asociativa]

-- Demostraciones en Lean4
-- =======================

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
calc
  a * (b * c)
    = (a * b) * c := by rw [←mul_assoc]
  _ = (b * a) * c := by rw [mul_comm a b]
  _ = b * (a * c) := by rw [mul_assoc]

-- 2ª demostración
example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
by
  rw [←mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- 3ª demostración
example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
by ring

-- Lemas usados
-- ============

-- #check (mul_comm : ∀ (a b : ℝ), a * b = b * a)
-- #check (mul_assoc : ∀ (a b c : ℝ), (a * b) * c = a * (b * c))
