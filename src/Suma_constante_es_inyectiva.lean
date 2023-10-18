-- Suma_constante_es_inyectiva.lean
-- La función (x ↦ x + c) es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, para todo c la función
--    f(x) = x + c
-- es inyectiva
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el lema
--    (∀ a, b, c) [a + b = c + b → a = c]                            (L1)
-- Hay que demostrar que
--    (∀ x₁ x₂) [f(x₁) = f(x₂) → x₁ = x₂]
-- Sean x₁, x₂ tales que f(x₁) = f(x₂). Entonces,
--    x₁ + c = x₂ + c
-- y, por L1, x₁ = x₂.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
open Function

variable {c : ℝ}

-- 1ª demostración
example : Injective ((. + c)) :=
by
  intro (x1 : ℝ) (x2 : ℝ) (h1 : x1 + c = x2 + c)
  show x1 = x2
  exact add_right_cancel h1

-- 2ª demostración
example : Injective ((. + c)) :=
by
  intro x1 x2 h1
  show x1 = x2
  exact add_right_cancel h1

-- 3ª demostración
example : Injective ((. + c)) :=
  fun _ _ h ↦ add_right_cancel h

-- Lemas usados
-- ============

-- variable {a b : ℝ}
-- #check (add_right_cancel : a + b = c + b → a = c)
