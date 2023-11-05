-- Asimetria_de_menor.lean
-- En ℝ, a < b → ¬(b < a).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que para todo par de numero reales a y b, si a < b entonces
-- no se tiene que b < a.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por hipótesis a < b y tenemos que demostrar que ¬(b < a). Supongamos
-- que b < a. Entonces, por la propiedad transiva a < a que es una
-- contradicción con la propiedad irreflexiva.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- 1ª demostración
example
  (h : a < b)
  : ¬ b < a :=
by
  intro h1
  -- h1 : b < a
  -- ⊢ False
  have : a < a := lt_trans h h1
  apply lt_irrefl a this

-- 2ª demostración
example
  (h : a < b)
  : ¬ b < a :=
by
  intro h1
  -- h1 : b < a
  -- ⊢ False
  exact lt_irrefl a (lt_trans h h1)

-- 3ª demostración
example
  (h : a < b)
  : ¬ b < a :=
fun h1 ↦ lt_irrefl a (lt_trans h h1)

-- 4ª demostración
example
  (h : a < b)
  : ¬ b < a :=
lt_asymm h

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (lt_asymm : a < b → ¬b < a)
-- #check (lt_irrefl a : ¬a < a)
-- #check (lt_trans : a < b → b < c → a < c)
