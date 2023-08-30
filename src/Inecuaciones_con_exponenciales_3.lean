-- Inecuaciones_con_exponenciales_3.lean
-- En ℝ, si d ≤ f, entonces c + e^(a + d) ≤ c + e^(a + f).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, c, d y f son números reales tales que
--    d ≤ f
-- entonces
--    c + exp (a + d) ≤ c + exp (a + f)
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- De la hipótesis, por la monotonia de la suma, se tiene
--    a + d ≤ a + f
-- que, por la monotonía de la exponencial, da
--    exp (a + d) ≤ exp (a + f)
-- y, por la monotonía de la suma, se tiene
--    c + exp (a + d) ≤ c + exp (a + f)

-- 2ª demostración en LN
-- =====================

-- Tenemos que demostrar que
--    c + exp (a + d) ≤ c + exp (a + f)
-- Por la monotonía de la suma, se reduce a
--    exp (a + d) ≤ exp (a + f)
-- que, por la monotonía de la exponencial, se reduce a
--    a + d ≤ a + f
-- que, por la monotonía de la suma, se reduce a
--    d ≤ f
-- que es la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a c d f : ℝ)

-- 1ª demostración
example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by
  have h1 : a + d ≤ a + f :=
    add_le_add_left h a
  have h2 : exp (a + d) ≤ exp (a + f) :=
    exp_le_exp.mpr h1
  show c + exp (a + d) ≤ c + exp (a + f)
  exact add_le_add_left h2 c

-- 2ª demostración
example
  (h : d ≤ f)
  : c + exp (a + d) ≤ c + exp (a + f) :=
by
  apply add_le_add_left
  apply exp_le_exp.mpr
  apply add_le_add_left
  exact h

-- Lemas usados
-- ============

-- variable (b : ℝ)
-- #check (add_le_add_left : b ≤ c → ∀ (a : ℝ), a + b ≤ a + c)
-- #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
