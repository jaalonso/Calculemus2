-- Producto_por_inverso.lean
-- Si G es un grupo y a ∈ G, entonces aa⁻¹ = 1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, se declara que G es un grupo mediante la expresión
--    variable {G : Type _} [Group G]
--
-- Como consecuencia, se tiene los siguientes axiomas
--    mul_assoc :    ∀ a b c : G, a * b * c = a * (b * c)
--    one_mul :      ∀ a : G, 1 * a = a
--    inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
--
-- Demostrar que si G es un grupo y a ∈ G, entonces
--    a * a⁻¹ = 1
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a·a⁻¹ = 1·(a·a⁻¹)                 [por producto con uno]
--          = (1·a)·a⁻¹                 [por asociativa]
--          = (((a⁻¹)⁻¹·a⁻¹) ·a)·a⁻¹    [por producto con inverso]
--          = ((a⁻¹)⁻¹·(a⁻¹ ·a))·a⁻¹    [por asociativa]
--          = ((a⁻¹)⁻¹·1)·a⁻¹           [por producto con inverso]
--          = (a⁻¹)⁻¹·(1·a⁻¹)           [por asociativa]
--          = (a⁻¹)⁻¹·a⁻¹               [por producto con uno]
--          = 1                         [por producto con inverso]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

-- 1ª demostración
example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                := by rw [one_mul]
        _ = (1 * a) * a⁻¹                := by rw [mul_assoc]
        _ = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ := by rw [inv_mul_cancel]
        _ = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ := by rw [← mul_assoc]
        _ = ((a⁻¹)⁻¹ * 1) * a⁻¹          := by rw [inv_mul_cancel]
        _ = (a⁻¹)⁻¹ * (1 * a⁻¹)          := by rw [mul_assoc]
        _ = (a⁻¹)⁻¹ * a⁻¹                := by rw [one_mul]
        _ = 1                            := by rw [inv_mul_cancel]

-- 2ª demostración
example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                := by simp
        _ = (1 * a) * a⁻¹                := by simp
        _ = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ := by simp
        _ = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ := by simp
        _ = ((a⁻¹)⁻¹ * 1) * a⁻¹          := by simp
        _ = (a⁻¹)⁻¹ * (1 * a⁻¹)          := by simp
        _ = (a⁻¹)⁻¹ * a⁻¹                := by simp
        _ = 1                            := by simp

-- 3ª demostración
example : a * a⁻¹ = 1 :=
by simp

-- 4ª demostración
example : a * a⁻¹ = 1 :=
by exact mul_inv_cancel a

-- Lemas usados
-- ============

-- variable (c : G)
-- #check (inv_mul_cancel a : a⁻¹  * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_inv_cancel a : a * a⁻¹ = 1)
-- #check (one_mul a : 1 * a = a)
