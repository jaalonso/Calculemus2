-- Doble_me_suma_cuadrados.lean
-- En ℝ, 2ab ≤ a² + b²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a y b números reales. Demostrar que
--    2ab ≤ a² + b²
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que los cuadrados son positivos, se tiene
--    (a - b)² ≥ 0
-- Desarrollando el cuadrado, se obtiene
--    a² - 2ab + b² ≥ 0
-- Sumando 2ab a ambos lados, queda
--    a² + b² ≥ 2ab

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

-- 1ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
by
  have h1 : 0 ≤ (a - b)^2         := sq_nonneg (a - b)
  have _h2 : 0 ≤ a^2 - 2*a*b + b^2 := by linarith only [h1]
  show 2*a*b ≤ a^2 + b^2
  linarith

-- 2ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  { calc a^2 - 2*a*b + b^2
         = (a - b)^2                 := (sub_sq a b).symm
       _ ≥ 0                         := sq_nonneg (a - b) }
  calc 2*a*b
       = 2*a*b + 0                   := (add_zero (2*a*b)).symm
     _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
     _ = a^2 + b^2                   := by ring

-- 3ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  { calc a^2 - 2*a*b + b^2
         = (a - b)^2       := (sub_sq a b).symm
       _ ≥ 0               := sq_nonneg (a - b) }
  linarith only [h]

-- 4ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
-- by apply?
two_mul_le_add_sq a b

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (add_zero a : a + 0 = a)
-- #check (sq_nonneg a : 0 ≤ a ^ 2)
-- #check (sub_sq a b : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2)
-- #check (two_mul_le_add_sq a b : 2 * a * b ≤ a ^ 2 + b ^ 2)
