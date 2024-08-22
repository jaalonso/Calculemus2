-- abs_sub.lean
-- En ℝ, |a| - |b| ≤ |a - b|
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a y b números reales. Demostrar que
--    |a| - |b| ≤ |a - b|
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Por la siguiente cadena de desigualdades
--    |a| - |b| = |a - b + b| - |b|
--              ≤ (|a - b| + |b|) - |b|   [por la desigualdad triangular]
--              = |a - b|

-- 2ª demostración en LN
-- =====================

-- Por la desigualdad triangular
--    |a - b + b| ≤ |a - b| + |b|
-- simplificando en la izquierda
--    |a| ≤ |a - b| + |b|
-- y, pasando |b| a la izquierda
--    |a| - |b| ≤ |a - b|

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- 1ª demostración (basada en la 1ª en LN)
example : |a| - |b| ≤ |a - b| :=
calc |a| - |b|
     = |a - b + b| - |b| :=
          congrArg (fun x => |x| - |b|) (sub_add_cancel a b).symm
   _ ≤ (|a - b| + |b|) - |b| :=
           sub_le_sub_right (abs_add (a - b) b) (|b|)
   _ = |a - b| :=
          add_sub_cancel_right (|a - b|) (|b|)

-- 2ª demostración (basada en la 1ª en LN)
example : |a| - |b| ≤ |a - b| :=
calc |a| - |b|
     = |a - b + b| - |b| := by
          rw [sub_add_cancel]
   _ ≤ (|a - b| + |b|) - |b| := by
          apply sub_le_sub_right
          apply abs_add
   _ = |a - b| := by
          rw [add_sub_cancel_right]

-- 3ª demostración (basada en la 2ª en LN)
example : |a| - |b| ≤ |a - b| :=
by
  have h1 : |a - b + b| ≤ |a - b| + |b| := abs_add (a - b) b
  rw [sub_add_cancel] at h1
  exact abs_sub_abs_le_abs_sub a b

-- 4ª demostración
example : |a| - |b| ≤ |a - b| :=
abs_sub_abs_le_abs_sub a b

-- Lemas usados
-- ============

-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_sub_abs_le_abs_sub a b : |a| - |b| ≤ |a - b|)
-- #check (add_sub_cancel_right a b : a + b - b = a)
-- #check (sub_add_cancel a b : a - b + b = a)
-- #check (sub_le_sub_right : a ≤ b → ∀ (c : ℝ), a - c ≤ b - c)
