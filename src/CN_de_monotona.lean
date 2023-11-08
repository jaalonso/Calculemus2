-- CN_de_monotona.lean
-- Si f es monótona y f(a) < f(b), entonces a < b.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es monótona y f(a) < f(b), entonces a < b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los lemas
--    a ≱ b → a < b                                                  (L1)
--    a ≥ b → a ≮ b                                                  (L2)
--
-- Usando el lema L1, basta demostrar que a ≱ b. Lo haremos por
-- reducción al absurdo. Para ello, supongamos que a ≥ b. Como f es
-- monótona, se tiene que f(a) ≥ f(b) y, aplicando el lema L2,
-- f(a) ≮ f(b), que contradice a la hipótesis.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (f : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  intro h3
  -- h3 : a ≥ b
  -- ⊢ False
  have h4 : f a ≥ f b := h1 h3
  have h5 : ¬ f a < f b := not_lt_of_ge h4
  exact h5 h2

-- 2ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  intro h3
  -- h3 : a ≥ b
  -- ⊢ False
  have h5 : ¬ f a < f b := not_lt_of_ge (h1 h3)
  exact h5 h2

-- 3ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  intro h3
  -- h3 : a ≥ b
  -- ⊢ False
  exact (not_lt_of_ge (h1 h3)) h2

-- 4ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
by
  apply lt_of_not_ge
  -- ⊢ ¬a ≥ b
  exact fun h3 ↦ (not_lt_of_ge (h1 h3)) h2

-- 5ª demostración
-- ===============

example
  (h1 : Monotone f)
  (h2 : f a < f b)
  : a < b :=
lt_of_not_ge (fun h3 ↦ (not_lt_of_ge (h1 h3)) h2)

-- Lemas usados
-- ============

-- #check (lt_of_not_ge : ¬ a ≥ b → a < b)
-- #check (not_lt_of_ge : a ≥ b → ¬ a < b)
