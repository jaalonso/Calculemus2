-- Condicion_para_no_positivo.lean
-- Si (∀ε > 0)[x ≤ ε], entonces x ≤ 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea x un número real tal que para todo número positivo ε, x ≤ ε
-- Demostrar que x ≤ 0.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Basta demostrar que x ≯ 0. Para ello, supongamos que x > 0 y vamos a
-- demostrar que
--    ¬(∀ε)[ε > 0 → x ≤ ε]                                       (1)
-- que es una contradicción con la hipótesis. Interiorizando la
-- negación, (1) es equivalente a
--    (∃ε)[ε > 0 ∧ ε < x]                                        (2)
-- Para demostrar (2) se puede elegir ε = x/2 ya que, como x > 0, se
-- tiene
--    0 < x/2 < x.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (x : ℝ)

-- 1ª demostración
-- ===============

example
  (h : ∀ ε > 0, x ≤ ε)
  : x ≤ 0 :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > 0
  intro hx0
  -- hx0 : x > 0
  -- ⊢ False
  apply absurd h
  -- ⊢ ¬∀ (ε : ℝ), ε > 0 → x ≤ ε
  push_neg
  -- ⊢ ∃ ε, ε > 0 ∧ ε < x
  use x /2
  -- ⊢ x / 2 > 0 ∧ x / 2 < x
  constructor
  { show x / 2 > 0
    exact half_pos hx0 }
  { show x / 2 < x
    exact half_lt_self hx0 }

-- 2ª demostración
-- ===============

example
  (x : ℝ)
  (h : ∀ ε > 0, x ≤ ε)
  : x ≤ 0 :=
by
  contrapose! h
  -- ⊢ ∃ ε, ε > 0 ∧ ε < x
  use x / 2
  -- ⊢ x / 2 > 0 ∧ x / 2 < x
  constructor
  { show x / 2 > 0
    exact half_pos h }
  { show x / 2 < x
    exact half_lt_self h }

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- variable (p q : Prop)
-- #check (le_of_not_gt : ¬a > b → a ≤ b)
-- #check (half_lt_self : 0 < a → a / 2 < a)
-- #check (half_pos : 0 < a → 0 < a / 2)
-- #check (absurd : p → ¬p → q)
