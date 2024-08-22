-- Introduccion_de_la_disyuncion_2.lean
-- En ℝ, -y > x² + 1 ⊢ y > 0 ∨ y < -1.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    -y > x^2 + 1
-- entonces
--    y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los siguientes lemas
--    (∀ b, c ∈ ℝ)[b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)]               (L1)
--    (∀ a ∈ ℝ)[0 ≤ a^2]                                             (L2)
--    (∀ a  ∈ ℝ)[0 + a = a]                                          (L3)
--    (∀ a, b ∈ ℝ)[a < -b ↔ b < -a]                                  (L4)

-- Se tiene
--    -y > x^2 + 1    [por la hipótesis]
--       ≥ 0 + 1      [por L1 y L2]
--       = 1          [por L3]
-- Por tanto,
--    -y > 1
-- y, aplicando el lema L4, se tiene
--    y < -1
-- Como se verifica la segunda parte de la diyunción, se verifica la
-- disyunción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1 : -y > 1 := by
    calc -y > x^2 + 1 := by exact h
          _ ≥ 0 + 1   := add_le_add_right (pow_two_nonneg x) 1
          _ = 1       := zero_add 1
  have h2: y < -1 := lt_neg.mp h1
  show y > 0 ∨ y < -1
  exact Or.inr h2

-- 2ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1 : -y > 1 := by linarith [pow_two_nonneg x]
  have h2: y < -1 := lt_neg.mp h1
  show y > 0 ∨ y < -1
  exact Or.inr h2

-- 3ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  have h1: y < -1 := by linarith [pow_two_nonneg x]
  show y > 0 ∨ y < -1
  exact Or.inr h1

-- 4ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by
  right
  -- ⊢ y < -1
  linarith [pow_two_nonneg x]

-- 5ª demostración
-- ===============

example
  (h : -y > x^2 + 1)
  : y > 0 ∨ y < -1 :=
by { right ; linarith [pow_two_nonneg x] }

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (lt_neg : a < -b ↔ b < -a)
-- #check (pow_two_nonneg a : 0 ≤ a ^ 2)
-- #check (zero_add a : 0 + a = a)
