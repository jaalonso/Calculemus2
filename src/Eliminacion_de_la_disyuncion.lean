-- Eliminacion_de_la_disyuncion.lean
-- En ℝ, si x < |y|, entonces x < y ó x < -y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que para todo par de números reales x e y, si x < |y|,
-- entonces x < y ó x < -y.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demostrará por casos según y ≥ 0.
--
-- Primer caso: Supongamos que y ≥ 0. Entonces, |y| = y y, por tanto,
-- x < y.
--
-- Segundo caso: Supongamos que y < 0. Entonces, |y| = -y y, por tanto,
-- x < -y.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable {x y : ℝ}

-- 1ª demostración
-- ===============

example : x < |y| → x < y ∨ x < -y :=
by
  intro h1
  -- h1 : x < |y|
  -- ⊢ x < y ∨ x < -y
  cases' le_or_gt 0 y with h2 h3
  . -- h2 : 0 ≤ y
    left
    -- ⊢ x < y
    rwa [abs_of_nonneg h2] at h1
  . -- h3 : 0 > y
    right
    -- ⊢ x < -y
    rwa [abs_of_neg h3] at h1

-- 2ª demostración
-- ===============

example : x < |y| → x < y ∨ x < -y :=
lt_abs.mp

-- Lemas usados
-- ============

-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (abs_of_nonneg : 0 ≤ x → abs x = x)
-- #check (abs_of_neg : x < 0 → abs x = -x)
-- #check (lt_abs : x < |y| ↔ x < y ∨ x < -y)
