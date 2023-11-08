-- CS_de_no_monotona.lean
-- Si a, b ∈ ℝ tales que a ≤ b y f(b) < f(a), entonces f no es monótona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b ∈ ℝ tales que (a ≤ b) y (f b < f a), entonces f
-- no es monótona.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el lema
--    a ≥ b → a ≮ b                                                (L1)
--
-- Lo demostraremos por reducción al absurdo. Para ello, supongamos que
-- f es monótona. Entonces, como a ≤ b, se tiene f(a) ≤ f(b) y, por el
-- lema L1, f b ≮ f a, en contradicción con la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (f : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by
  intro h3
  -- h3 : Monotone f
  -- ⊢ False
  have h4 : f a ≤ f b := h3 h1
  have h5 : ¬(f b < f a) := not_lt_of_ge h4
  exact h5 h2

-- 2ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by
  intro h3
  -- h3 : Monotone f
  -- ⊢ False
  have h5 : ¬(f b < f a) := not_lt_of_ge (h3 h1)
  exact h5 h2

-- 3ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
by
  intro h3
  -- h3 : Monotone f
  -- ⊢ False
  exact (not_lt_of_ge (h3 h1)) h2

-- 4ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : f b < f a)
  : ¬ Monotone f :=
fun h3 ↦ (not_lt_of_ge (h3 h1)) h2

-- Lemas usados
-- ============

-- #check (not_lt_of_ge : a ≥ b → ¬a < b)
