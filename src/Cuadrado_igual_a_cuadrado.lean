-- Cuadrado_igual_a_cuadrado.lean
-- En ℝ, x² = y² → x = y ∨ x = -y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    x^2 = y^2
-- entonces
--    x = y ∨ x = -y
-- ----------------------------------------------------------------------

-- Usaremos los siguientes lemas
--    (∀ x ∈ ℝ)[x - x = 0]                                           (L1)
--    (∀ x, y ∈ ℝ)[xy = 0 → x = 0 ∨ y = 0]                           (L2)
--    (∀ x, y ∈ ℝ)[x - y = 0 ↔ x = y]                                (L3)
--    (∀ x, y ∈ ℝ)[x + y = 0 → x = -y]                               (L4)
--
-- Se tiene que
--    (x - y)(x + y) = x² - y²
--                   = y² - y²    [por la hipótesis]
--                   = 0          [por L1]
-- y, por el lema L2, se tiene que
--    x - y = 0 ∨ x + y = 0
--
-- Acabaremos la demostración por casos.
--
-- Primer caso:
--   x - y = 0 ⟹ x = y             [por L3]
--             ⟹ x = y ∨ x = -y
--
-- Segundo caso:
--   x + y = 0 ⟹ x = -y            [por L4]
--             ⟹ x = y ∨ x = -y

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (x y : ℝ)

-- 1ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by
  have h1 : (x - y) * (x + y) = 0 := by
    calc (x - y) * (x + y) = x^2 - y^2 := by ring
                         _ = y^2 - y^2 := by rw [h]
                         _ = 0         := sub_self (y ^ 2)
  have h2 : x - y = 0 ∨ x + y = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  . -- h3 : x - y = 0
    left
    -- ⊢ x = y
    exact sub_eq_zero.mp h3
  . -- h4 : x + y = 0
    right
    -- ⊢ x = -y
    exact eq_neg_of_add_eq_zero_left h4

-- 2ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
by
  have h1 : (x - y) * (x + y) = 0 := by nlinarith
  have h2 : x - y = 0 ∨ x + y = 0 := by aesop
  rcases h2 with h3 | h4
  . -- h3 : x - y = 0
    left
    -- ⊢ x = y
    linarith
  . -- h4 : x + y = 0
    right
    -- ⊢ x = -y
    linarith

-- 2ª demostración
-- ===============

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
sq_eq_sq_iff_eq_or_eq_neg.mp h

-- Lemas usados
-- ============

-- #check (eq_neg_of_add_eq_zero_left : x + y = 0 → x = -y)
-- #check (eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0)
-- #check (sq_eq_sq_iff_eq_or_eq_neg : x ^ 2 = y ^ 2 ↔ x = y ∨ x = -y)
-- #check (sub_eq_zero : x - y = 0 ↔ x = y)
-- #check (sub_self x : x - x = 0)
