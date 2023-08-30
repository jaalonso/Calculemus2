-- Inecuaciones_con_exponenciales.lean
-- En ℝ, si 1 ≤ a y b ≤ d, entonces 2 + a + eᵇ ≤ 3a + eᵈ
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a, b, y d números reales. Demostrar  que si
--    1 ≤ a
--    b ≤ d
-- entonces
--    2 + a + exp b ≤ 3 * a + exp d
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- De la primera hipótesis (1 ≤ a), multiplicando por 2, se obtiene
--    2 ≤ 2a
-- y, sumando a ambos lados, se tiene
--    2 + a ≤ 3a             (1)
-- De la hipótesis 2 (b ≤ d) y de la monotonía de la función exponencial
-- se tiene
--    e^b ≤ e^d              (2)
-- Finalmente, de (1) y (2) se tiene
--    2 + a + e^b ≤ 3a + e^d

-- Demostraciones con Lean4
-- ========================

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b d : ℝ)

-- 1ª demostración
example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by
  have h3 : 2 + a ≤ 3 * a := calc
    2 + a = 2 * 1 + a := by linarith only []
        _ ≤ 2 * a + a := by linarith only [h1]
        _ ≤ 3 * a     := by linarith only []
  have h4 : exp b ≤ exp d := by
    linarith only [exp_le_exp.mpr h2]
  show 2 + a + exp b ≤ 3 * a + exp d
  exact add_le_add h3 h4

-- 2ª demostración
example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
calc
  2 + a + exp b
    ≤ 3 * a + exp b := by linarith only [h1]
  _ ≤ 3 * a + exp d := by linarith only [exp_le_exp.mpr h2]

-- 3ª demostración
example
  (h1 : 1 ≤ a)
  (h2 : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by linarith [exp_le_exp.mpr h2]

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
