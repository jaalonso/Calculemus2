-- Unicidad_de_inversos_en_monoides.lean
-- Unicidad de inversos en monoides conmutativos.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los monoides conmutativos, si un elemento tiene un
-- inverso por la derecha, dicho inverso es único.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    y = 1·y          [por neutro a la izquierda]
--      = (x·z)·y      [por hipótesis]
--      = (z·x)·y      [por la conmutativa]
--      = z·(x·y)      [por la asociativa]
--      = z·1          [por hipótesis]
--      = z            [por neutro a la derecha]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {M : Type} [CommMonoid M]
variable {x y z : M}

-- 1ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       := (one_mul y).symm
     _ = (x * z) * y := congrArg (. * y) hz.symm
     _ = (z * x) * y := congrArg (. * y) (mul_comm x z)
     _ = z * (x * y) := mul_assoc z x y
     _ = z * 1       := congrArg (z * .) hy
     _ = z           := mul_one z

-- 2ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y     := by simp only [one_mul]
   _ = (x * z) * y := by simp only [hz]
   _ = (z * x) * y := by simp only [mul_comm]
   _ = z * (x * y) := by simp only [mul_assoc]
   _ = z * 1       := by simp only [hy]
   _ = z           := by simp only [mul_one]

-- 3ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y     := by simp
   _ = (x * z) * y := by simp [hz]
   _ = (z * x) * y := by simp [mul_comm]
   _ = z * (x * y) := by simp [mul_assoc]
   _ = z * 1       := by simp [hy]
   _ = z           := by simp

-- 4ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
by
  apply left_inv_eq_right_inv _ hz
  -- ⊢ y * x = 1
  rw [mul_comm]
  -- ⊢ x * y = 1
  exact hy

-- 5ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
inv_unique hy hz

-- Lemas usados
-- ============

-- #check (inv_unique : x * y = 1 → x * z = 1 → y = z)
-- #check (left_inv_eq_right_inv : y * x = 1 → x * z = 1 → y = z)
-- #check (mul_assoc x y z : (x * y) * z = x * (y * z))
-- #check (mul_comm x y : x * y = y * x)
-- #check (mul_one x : x * 1 = x)
-- #check (one_mul x : 1 * x = x)
