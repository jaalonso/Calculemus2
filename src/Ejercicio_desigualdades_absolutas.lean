-- Ejercicio_desigualdades_absolutas.lean
-- En ℝ, |ab| ≤ (a²+b²)/2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a y b números reales. Demostrar que
--    |a*b| ≤ (a^2 + b^2) / 2
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Para demostrar
--    |ab| ≤ (a² + b² / 2
-- basta demostrar estas dos desigualdades
--    ab ≤ (a² + b²) / 2                                              (1)
--    -(ab) ≤ (a² + b²) / 2                                           (2)
--
-- Para demostrar (1) basta demostrar que
--    2ab ≤ a² + b²
-- que se prueba como sigue. En primer lugar, como los cuadrados son no
-- negativos, se tiene
--   (a - b)² ≥ 0
-- Desarrollando el cuandrado,
--   a² - 2ab + b² ≥ 0
-- Sumando 2ab,
--   a² + b² ≥ 2ab
--
-- Para demostrar (2) basta demostrar que
--    -2ab ≤ a² + b²
-- que se prueba como sigue. En primer lugar, como los cuadrados son no
-- negativos, se tiene
--   (a + b)² ≥ 0
-- Desarrollando el cuandrado,
--   a² + 2ab + b² ≥ 0
-- Restando 2ab,
--   a² + b² ≥ -2ab

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

-- Lemas auxiliares
-- ================

lemma aux1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2
      = (a - b) ^ 2            := by ring
    _ ≥ 0                      := pow_two_nonneg (a - b)
  linarith only [h]

lemma aux2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2
      = (a + b) ^ 2            := by ring
    _ ≥ 0                      := pow_two_nonneg (a + b)
  linarith only [h]

-- 1ª demostración
-- ===============

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  { have h1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := aux1 a b
    show a * b ≤ (a ^ 2 + b ^ 2) / 2
    exact (le_div_iff h).mpr h1 }
  { have h2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := aux2 a b
    show -(a * b) ≤ (a ^ 2 + b ^ 2) / 2
    exact (le_div_iff h).mpr h2 }

-- 2ª demostración
-- ===============

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  { exact (le_div_iff h).mpr (aux1 a b) }
  { exact (le_div_iff h).mpr (aux2 a b) }

-- 3ª demostración
-- ===============

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  { rw [le_div_iff h]
    apply aux1 }
  { rw [le_div_iff h]
    apply aux2 }

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (abs_le' : |a| ≤ b ↔ a ≤ b ∧ -a ≤ b)
-- #check (le_div_iff : 0 < c → (a ≤ b / c ↔ a * c ≤ b))
-- #check (pow_two_nonneg a : 0 ≤ a ^ 2)
