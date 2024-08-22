-- Desigualdad_logaritmica.lean
-- En ℝ, si a ≤ b, entonces log(1+e^a) ≤ log(1+e^b)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a y b son números reales tales que
--    a ≤ b
-- entonces
--    log(1+e^a) ≤ log(1+e^b)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la monotonía del logaritmo, basta demostrar que
--    0 < 1 + e^a                 (1)
--    1 + e^a ≤ 1 + e^b           (2)
--
-- La (1), por la suma de positivos, se reduce a
--    0 < 1                       (1.1)
--    0 < e^a                     (1.2)
-- La (1.1) es una propiedad de los números naturales y la (1.2) de la
-- función exponencial.
--
-- La (2), por la monotonía de la suma, se reduce a
--    e^a ≤ e^b
-- que, por la monotonía de la exponencial, se reduce a
--    a ≤ b
-- que es la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b : ℝ)

-- 1ª demostración
example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by
  have h1 : (0 : ℝ) < 1 :=
    zero_lt_one
  have h2 : 0 < exp a :=
    exp_pos a
  have h3 : 0 < 1 + exp a :=
    add_pos h1 h2
  have h4 : exp a ≤ exp b :=
    exp_le_exp.mpr h
  have h5 : 1 + exp a ≤ 1 + exp b :=
    add_le_add_left h4 1
  show log (1 + exp a) ≤ log (1 + exp b)
  exact log_le_log h3 h5

-- 2ª demostraciṕn
example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
by
  apply log_le_log
  { apply add_pos
    { exact zero_lt_one }
    { exact exp_pos a }}
  { apply add_le_add_left
    exact exp_le_exp.mpr h }

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (add_le_add_left : b ≤ c → ∀ (a : ℝ), a + b ≤ a + c)
-- #check (add_pos : 0 < a → 0 < b → 0 < a + b)
-- #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
-- #check (exp_pos a : 0 < exp a)
-- #check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
-- #check (zero_lt_one : 0 < 1)
