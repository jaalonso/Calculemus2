-- Cota_inf2_de_abs.lean
-- En ℝ, -x ≤ |x|.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    -x ≤ |x|
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--    (∀ x ∈ ℝ)[0 ≤ x → -x ≤ x]                                      (L1)
--    (∀ x ∈ ℝ)[0 ≤ x → |x| = x]                                     (L2)
--    (∀ x ∈ ℝ)[x ≤ x]                                               (L3)
--    (∀ x ∈ ℝ)[x < 0 → |x| = -x]                                    (L4)
--
-- Se demostrará por casos según x ≥ 0:
--
-- Primer caso: Supongamos que x ≥ 0. Entonces,
--    -x ≤ x      [por L1]
--       = |x|    [por L2]
--
-- Segundo caso: Supongamos que x < 0. Entonces,
--    -x ≤ -x     [por L3]
--     _ = |x|    [por L4]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x : ℝ}

-- 1ª demostración
-- ===============

example : -x ≤ |x| :=
by
  cases' (le_or_gt 0 x) with h1 h2
  . -- h1 : 0 ≤ x
    show -x ≤ |x|
    calc -x ≤ x   := by exact neg_le_self h1
          _ = |x| := (abs_of_nonneg h1).symm
  . -- h2 : 0 > x
    show -x ≤ |x|
    calc -x ≤ -x  := by exact le_refl (-x)
          _ = |x| := (abs_of_neg h2).symm

-- 2ª demostración
-- ===============

example : -x ≤ |x| :=
by
  cases' (le_or_gt 0 x) with h1 h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
    -- ⊢ -x ≤ x
    exact neg_le_self h1
  . -- h2 : 0 > x
    rw [abs_of_neg h2]

-- 3ª demostración
-- ===============

example : -x ≤ |x| :=
by
  rcases (le_or_gt 0 x) with h1 | h2
  . -- h1 : 0 ≤ x
    rw [abs_of_nonneg h1]
    -- ⊢ -x ≤ x
    linarith
  . -- h2 : 0 > x
    rw [abs_of_neg h2]

-- 4ª demostración
-- ===============

example : -x ≤ |x| :=
  neg_le_abs x

-- Lemas usados
-- ============

-- variable (y : ℝ)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (le_refl x : x ≤ x)
-- #check (neg_le_abs x : -x ≤ |x|)
-- #check (neg_le_self : 0 ≤ x → -x ≤ x)
