-- Producto_por_uno.lean
-- Si G es un grupo y a ∈ G, entonces a·1 = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si G es un grupo y a ∈ G, entonces
--    a * 1 = a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se tiene por la siguiente cadena de igualdades
--    a·1 = a·(a⁻¹·a)    [por producto con inverso]
--        = (a·a⁻¹)·a    [por asociativa]
--        = 1·a          [por producto con inverso]
--        = a            [por producto con uno]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

-- 1ª demostración
example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) := by rw [inv_mul_cancel]
      _ = (a * a⁻¹) * a := by rw [mul_assoc]
      _ = 1 * a         := by rw [mul_inv_cancel]
      _ = a             := by rw [one_mul]

-- 2ª demostración
example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) := by simp
      _ = (a * a⁻¹) * a := by simp
      _ = 1 * a         := by simp
      _ = a             := by simp

-- 3ª demostración
example : a * 1 = a :=
by simp

-- 4ª demostración
example : a * 1 = a :=
by exact mul_one a

-- Lemas usados
-- ============

-- variable (c : G)
-- #check (inv_mul_cancel a : a⁻¹  * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_inv_cancel a : a * a⁻¹ = 1)
-- #check (one_mul a : 1 * a = a)
-- #check (mul_one a : a * 1 = a)
