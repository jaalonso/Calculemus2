-- Cadena_de_desigualdades.lean
-- En ℝ, si a ≤ b, b < c, c ≤ d y d < e, entonces a < e.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b, c, d y e son números reales tales que
--    a ≤ b,
--    b < c,
--    c ≤ d y
--    d < e,
-- entonces
--    a < e.
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Por la siguiente cadena de desigualdades
--    a ≤ b    [por h1]
--      < c    [por h2]
--      ≤ d    [por h3]
--      < e    [por h4]

-- 2ª demostración en LN
-- =====================

-- A partir de las hipótesis 1 (a ≤ b) y 2 (b < c) se tiene
--    a < c
-- que, junto la hipótesis 3 (c ≤ d) da
--    a < d
-- que, junto la hipótesis 4 (d < e) da
--    a < e.

-- 3ª demostración en LN
-- =====================

-- Para demostrar a < e, por la hipótesis 1 (a ≤ b) se reduce a probar
--    b < e
-- que, por la hipótesis 2 (b < c), se reduce a
--    c < e
-- que, por la hipótesis 3 (c ≤ d), se reduce a
--    d < e
-- que es cierto, por la hipótesis 4.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d e : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
calc
  a ≤ b := h1
  _ < c := h2
  _ ≤ d := h3
  _ < e := h4

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
by
  have h5 : a < c := lt_of_le_of_lt h1 h2
  have h6 : a < d := lt_of_lt_of_le h5 h3
  show a < e
  exact lt_trans h6 h4

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
by
  apply lt_of_le_of_lt h1
  apply lt_trans h2
  apply lt_of_le_of_lt h3
  exact h4

-- El desarrollo de la prueba es
--
--    a b c d e : ℝ,
--    h1 : a ≤ b,
--    h2 : b < c,
--    h3 : c ≤ d,
--    h4 : d < e
--    ⊢ a < e
-- apply lt_of_le_of_lt h1,
--    ⊢ b < e
-- apply lt_trans h2,
--    ⊢ c < e
-- apply lt_of_le_of_lt h3,
--    ⊢ d < e
-- exact h4,
--    no goals

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : b < c)
  (h3 : c ≤ d)
  (h4 : d < e) :
  a < e :=
by linarith

-- Lemas usados
-- ============

-- #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
-- #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
-- #check (lt_trans : a < b → b < c → a < c)
