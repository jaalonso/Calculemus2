-- Reto_13.lean
-- Desigualdad triangular inversa: ||x| - |y|| ≤ |x - y|.
-- Sevilla, 9-agosto-2026
-- -----------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar la desigualdad triangular inversa; es decir, que para
-- cualesquiera números reales x e y, se cumple la siguiente relación:
--    ||x| - |y|| ≤ |x - y|
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Para demostrar que
--    ||x| - |y|| ≤ |x - y|
-- es suficiente demostrar estas dos desigualdades
--    |x| - |y| ≤ |x - y|
--     -(|x| - |y|) ≤ |x - y|
--
-- La demostración de la primera es
--    |x| - |y|
--    = |(x - y) + y| - |y|
--    ≤ (|x - y| + |y|) - |y|    [por desigualdad triangular]
--    = |x - y|
-- y la de la segunda es
--    -(|x| - |y|)
--    = |y| - |x|
--    = |x - (x - y)| - |x|
--    ≤ (|x| + |x - y|) - |x|    [por desigualdad triangular]
--    = |x - y|

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (x y : ℝ)

-- 1ª demostración
-- ===============

example : |(|x| - |y|)| ≤ |x - y| :=
by
  grind

-- 2ª demostración
-- ===============

example :
  |(|x| - |y|)| ≤ |x - y| :=
by
  rw [abs_le']
  -- ⊢ |x| - |y| ≤ |x - y| ∧ -(|x| - |y|) ≤ |x - y|
  constructor
  · -- ⊢ |x| - |y| ≤ |x - y|
    grind
  · -- ⊢ -(|x| - |y|) ≤ |x - y|
    grind

-- 3ª demostración
-- ===============

example :
  |(|x| - |y|)| ≤ |x - y| :=
by
  rw [abs_le']
  -- ⊢ |x| - |y| ≤ |x - y| ∧ -(|x| - |y|) ≤ |x - y|
  constructor
  · -- ⊢ |x| - |y| ≤ |x - y|
    calc |x| - |y|
         = |(x - y) + y| - |y|   := by grind
       _ ≤ (|x - y| + |y|) - |y| := by grind
       _ = |x - y|               := by grind
  · -- ⊢ -(|x| - |y|) ≤ |x - y|
    calc -(|x| - |y|)
         = |y| - |x|             := by grind
       _ = |x - (x - y)| - |x|   := by grind
       _ ≤ (|x| + |x - y|) - |x| := by grind
       _ = |x - y|               := by grind

-- 4ª demostración
-- ===============

example :
  |(|x| - |y|)| ≤ |x - y| :=
by
  rw [abs_le']
  -- ⊢ |x| - |y| ≤ |x - y| ∧ -(|x| - |y|) ≤ |x - y|
  constructor
  · -- ⊢ |x| - |y| ≤ |x - y|
    calc |x| - |y|
         = |(x - y) + y| - |y|   := by congr ; ring
       _ ≤ (|x - y| + |y|) - |y| := sub_le_sub_right (abs_add_le (x - y) y) |y|
       _ = |x - y|               := by ring
  · -- ⊢ -(|x| - |y|) ≤ |x - y|
    calc -(|x| - |y|)
         = |y| - |x|             := by ring
       _ = |x - (x - y)| - |x|   := by congr ; ring
       _ ≤ (|x| + |x - y|) - |x| := sub_le_sub_right (abs_sub x (x - y)) |x|
       _ = |x - y|               := by ring

-- 5ª demostración
-- ===============

example :
  |(|x| - |y|)| ≤ |x - y| :=
by
  rw [abs_le']
  -- ⊢ |x| - |y| ≤ |x - y| ∧ -(|x| - |y|) ≤ |x - y|
  constructor
  · -- ⊢ |x| - |y| ≤ |x - y|
    calc |x| - |y|
         = |(x - y) + y| - |y|   := congrArg (|·| - |y|) (sub_add_cancel x y).symm
       _ ≤ (|x - y| + |y|) - |y| := sub_le_sub_right (abs_add_le (x - y) y) |y|
       _ = |x - y|               := add_sub_cancel_right |x - y| |y|
  · -- ⊢ -(|x| - |y|) ≤ |x - y|
    calc -(|x| - |y|)
         = |y| - |x|             := neg_sub |x| |y|
       _ = |x - (x - y)| - |x|   := congrArg (|·| - |x|) (sub_sub_self x y).symm
       _ ≤ (|x| + |x - y|) - |x| := sub_le_sub_right (abs_sub x (x - y)) |x|
       _ = |x - y|               := add_sub_cancel_left |x| |x - y|

-- 6ª demostración
-- ===============

example : |(|x| - |y|)| ≤ |x - y| :=
abs_abs_sub_abs_le x y

-- Lemas usados
-- ============

variable (f : ℝ → ℝ)
#check (abs_abs_sub_abs_le x y : |(|x| - |y|)| ≤ |x - y|)
#check (abs_add_le x y : |x + y| ≤ |x| + |y|)
#check (abs_le' : |x| ≤ y ↔ x ≤ y ∧ -x ≤ y)
#check (abs_sub x y : |x - y| ≤ |x| + |y|)
#check (add_sub_cancel_left x y : (x + y) - x = y)
#check (add_sub_cancel_right x y : (x + y) - y = x)
#check (congrArg f : x = y → f x = f y)
#check (neg_sub x y : -(x - y) = y - x)
#check (sub_add_cancel x y: (x - y) + y = x)
#check (sub_le_sub_right : x ≤ y → ∀ z, x - z ≤ y - z)
#check (sub_sub_self x y : x - (x - y) = y)
