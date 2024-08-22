-- Introduccion_de_la_disyuncion_1.lean
-- En ℝ, y > x^2 ⊢ y > 0 ∨ y < -1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    y > x^2
-- entonces
--    y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que
--    (∀ x ∈ ℝ)[x² ≥ 0]
-- se tiene que
--    y > x²
--      ≥ 0
-- Por tanto, y > 0 y, al verificar la primera parte de la diyunción, se
-- verifica la disyunción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  have h1 : y > 0 := by
    calc y > x^2 := h
         _ ≥ 0   := pow_two_nonneg x
  show y > 0 ∨ y < -1
  exact Or.inl h1

-- 2ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  calc y > x^2 := h
       _ ≥ 0   := pow_two_nonneg x

-- 3ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by
  left
  -- ⊢ y > 0
  linarith [pow_two_nonneg x]

-- 4ª demostración
-- ===============

example
  (h : y > x^2)
  : y > 0 ∨ y < -1 :=
by { left ; linarith [pow_two_nonneg x] }

-- Lema usado
-- ==========

-- #check (pow_two_nonneg x : 0 ≤ x ^ 2)
