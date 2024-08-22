-- Desigualdad_triangular_para_valor_absoluto.lean
-- En ℝ, |x + y| ≤ |x| + |y|.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    |x + y| ≤ |x| + |y|
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--     (∀ x ∈ ℝ)[0 ≤ x → |x| = x]                          (L1)
--     (∀ a, b, c, d ∈ ℝ)[a ≤ b ∧ c ≤ d → a + c ≤ b + d]   (L2)
--     (∀ x ∈ ℝ)[x ≤ |x|]                                  (L3)
--     (∀ x ∈ ℝ)[x < 0 → |x| = -x]                         (L4)
--     (∀ x, y ∈ ℝ)[-(x + y) = -x + -y]                    (L5)
--     (∀ x ∈ ℝ)[-x ≤ |x|]                                 (L6)
--
-- Se demostrará por casos según x + y ≥ 0:
--
-- Primer caso: Supongamos que x + y ≥ 0. Entonces,
--    |x + y| = x + y        [por L1]
--          _ ≤ |x| + |y|    [por L2 y L3]
--
-- Segundo caso: Supongamos que x + y < 0. Entonces,
--    |x + y| = -(x + y)     [por L4]
--            = -x + -y      [por L5]
--            ≤ |x| + |y|    [por L2 y L6]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| :=
by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    show |x + y| ≤ |x| + |y|
    calc |x + y| = x + y     := by exact abs_of_nonneg h1
               _ ≤ |x| + |y| := add_le_add (le_abs_self x) (le_abs_self y)
  . -- h2 : 0 > x + y
    show |x + y| ≤ |x| + |y|
    calc |x + y| = -(x + y)  := by exact abs_of_neg h2
               _ = -x + -y   := by exact neg_add x y
               _ ≤ |x| + |y| := add_le_add (neg_le_abs x) (neg_le_abs y)

-- 2ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    rw [abs_of_nonneg h1]
    -- ⊢ x + y ≤ |x| + |y|
    exact add_le_add (le_abs_self x) (le_abs_self y)
  . -- h2 : 0 > x + y
    rw [abs_of_neg h2]
    -- ⊢ -(x + y) ≤ |x| + |y|
    calc -(x + y) = -x + -y    := by exact neg_add x y
                _ ≤ |x| + |y|  := add_le_add (neg_le_abs x) (neg_le_abs y)

-- 2ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h1 | h2
  · -- h1 : 0 ≤ x + y
    rw [abs_of_nonneg h1]
    -- ⊢ x + y ≤ |x| + |y|
    linarith [le_abs_self x, le_abs_self y]
  . -- h2 : 0 > x + y
    rw [abs_of_neg h2]
    -- ⊢ -(x + y) ≤ |x| + |y|
    linarith [neg_le_abs x, neg_le_abs y]

-- 3ª demostración
-- ===============

example : |x + y| ≤ |x| + |y| :=
  abs_add x y

-- Lemas usados
-- ============

-- variable (a b c d : ℝ)
-- #check (abs_add x y : |x + y| ≤ |x| + |y|)
-- #check (abs_of_neg : x < 0 → |x| = -x)
-- #check (abs_of_nonneg : 0 ≤ x → |x| = x)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (le_abs_self a : a ≤ |a|)
-- #check (le_or_gt x y : x ≤ y ∨ x > y)
-- #check (neg_add x y : -(x + y) = -x + -y)
-- #check (neg_le_abs x : -x ≤ |x|)
