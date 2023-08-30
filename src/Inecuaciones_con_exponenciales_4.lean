-- Inecuaciones_con_exponenciales_4.lean
-- En ℝ, si a ≤ b, entonces c - e^b ≤ c - e^a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a, b y c números reales. Demostrar que si
--    a ≤ b
-- entonces
--    c - e^b ≤ c - e^a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Aplicando la monotonía de la exponencial a la hipótesis, se tiene
--    e^a ≤ e^b
-- y, restando de c, se invierte la desigualdad
--    c - e^b ≤ c - e^a

-- Demostraciones con Lean4
-- ========================

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

variable (a b c : ℝ)

-- 1ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by
   have h1 : exp a ≤ exp b :=
     exp_le_exp.mpr h
   show c - exp b ≤ c - exp a
   exact sub_le_sub_left h1 c

-- 2ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by
   apply sub_le_sub_left _ c
   apply exp_le_exp.mpr h

-- 3ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
sub_le_sub_left (exp_le_exp.mpr h) c

-- 4ª demostración
example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

-- Lemas usados
-- ============

-- #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
-- #check (sub_le_sub_left : a ≤ b → ∀ (c : ℝ), c - b ≤ c - a)
