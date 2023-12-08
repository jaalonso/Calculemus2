-- Menor_por_intermedio.lean
-- Si (∃z ∈ ℝ)[x < z < y], entonces x < y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si (∃z ∈ ℝ)[x < z < y], entonces x < y.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea z tal que verifica las siguientes relaciones:
--    x < z                                                          (1)
--    z < y                                                          (2)
-- Aplicando la propiedad transitiva a (1) y (2) se tiene que
--    x < y.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable (x y : ℝ)

-- 1ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by
  rintro ⟨z, h1 : x < z, h2 : z < y⟩
  show x < y
  exact lt_trans h1 h2

-- 2ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
by
  rintro ⟨z, h1, h2⟩
  exact lt_trans h1 h2

-- 3ª demostración
-- ===============

example : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
fun ⟨_, h1, h2⟩ ↦ lt_trans h1 h2

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (lt_trans : a < b → b < c → a < c)
