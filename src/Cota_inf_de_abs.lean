-- Cota_inf_de_abs.lean
-- En ℝ, x ≤ |x|.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en ℝ,
--    x ≤ |x|
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--    (∀ x ∈ ℝ)[0 ≤ x → |x| = x]                                     (L1)
--    (∀ x, y ∈ ℝ)[x < y → x ≤ y]                                    (L2)
--    (∀ x ∈ ℝ)[x ≤ 0 → x ≤ -x]                                      (L3)
--    (∀ x ∈ ℝ)[x < 0 → |x| = -x]                                    (L4)
--
-- Se demostrará por casos según x ≥ 0:
--
-- Primer caso: Supongamos que x ≥ 0. Entonces,
--    x ≤ x
--      = |x|    [por L1]
--
-- Segundo caso: Supongamos que x < 0. Entonces, por el L2, se tiene
--    x ≤ 0                                                          (1)
-- Por tanto,
--    x ≤ -x     [por L3 y (1)]
--      = |x|    [por L4]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x : ℝ}

-- 1ª demostración
-- ===============

example : x ≤ |x| :=
by
  cases' le_or_gt 0 x with h1 h2
  . -- h1 : 0 ≤ x
    show x ≤ |x|
    calc x ≤ x   := le_refl x
         _ = |x| := (abs_of_nonneg h1).symm
  . -- h2 : 0 > x
    have h3 : x ≤ 0 := le_of_lt h2
    show x ≤ |x|
    calc x ≤ -x  := le_neg_self_iff.mpr h3
         _ = |x| := (abs_of_neg h2).symm

-- 2ª demostración
-- ===============

example : x ≤ |x| :=
by
  cases' le_or_gt 0 x with h1 h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
  . -- h2 : 0 > x
    rw [abs_of_neg h2]
    -- ⊢ x ≤ -x
    apply Left.self_le_neg
    -- ⊢ x ≤ 0
    exact le_of_lt h2

-- 3ª demostración
-- ===============

example : x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
  . -- h1 : 0 ≤ x
    rw [abs_of_neg h2]
    linarith

-- 4ª demostración
-- ===============

example : x ≤ |x| :=
  le_abs_self x

-- Lemas usados
-- ============

-- variable (y : ℝ)
-- #check (Left.self_le_neg : x ≤ 0 → x ≤ -x)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (le_abs_self x : x ≤ |x|)
-- #check (le_neg_self_iff : x ≤ -x ↔ x ≤ 0)
-- #check (le_of_lt : x < y → x ≤ y)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
