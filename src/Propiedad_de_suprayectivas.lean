-- Propiedad_de_suprayectivas.lean
-- Si f: ℝ → ℝ es suprayectiva, entonces ∃x ∈ ℝ tal que f(x)² = 9
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es una función suprayectiva de ℝ en ℝ,
-- entonces existe un x tal que (f x)^2 = 9.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Al ser f suprayectiva, existe un y tal que f(y) = 3. Por tanto,
-- f(y)² = 9.

-- Demostración con Lean4
-- ======================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Function

example
  {f : ℝ → ℝ}
  (h : Surjective f)
  : ∃ x, (f x)^2 = 9 :=
by
  cases' h 3 with y hy
  -- y : ℝ
  -- hy : f y = 3
  use y
  -- ⊢ f y ^ 2 = 9
  rw [hy]
  -- ⊢ 3 ^ 2 = 9
  norm_num
