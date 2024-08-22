-- Inverso_del_producto.lean
-- Si G es un grupo y a, b ∈ G, entonces (ab)⁻¹ = b⁻¹a⁻¹
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si G es un grupo y a, b ∈ G, entonces
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Teniendo en cuenta la propiedad
--    (∀ a, b ∈ R)[ab = 1 → a⁻¹ = b]
-- basta demostrar que
--    (a·b)·(b⁻¹·a⁻¹) = 1.
-- que se demuestra mediante la siguiente cadena de igualdades
--    (a·b)·(b⁻¹·a⁻¹) =  a·(b·(b⁻¹·a⁻¹))   [por la asociativa]
--                    =  a·((b·b⁻¹)·a⁻¹)   [por la asociativa]
--                    =  a·(1·a⁻¹)         [por producto con inverso]
--                    =  a·a⁻¹             [por producto con uno]
--                    =  1                 [por producto con inverso]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

lemma aux : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
calc
  (a * b) * (b⁻¹ * a⁻¹)
    = a * (b * (b⁻¹ * a⁻¹)) := by rw [mul_assoc]
  _ = a * ((b * b⁻¹) * a⁻¹) := by rw [mul_assoc]
  _ = a * (1 * a⁻¹)         := by rw [mul_inv_cancel]
  _ = a * a⁻¹               := by rw [one_mul]
  _ = 1                     := by rw [mul_inv_cancel]

-- 1ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
    aux a b
  show (a * b)⁻¹ = b⁻¹ * a⁻¹
  exact inv_eq_of_mul_eq_one_right h1

-- 2ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
    aux a b
  show (a * b)⁻¹ = b⁻¹ * a⁻¹
  simp [h1]

-- 3ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 :=
    aux a b
  simp [h1]

-- 4ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by
  apply inv_eq_of_mul_eq_one_right
  rw [aux]

-- 5ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by exact mul_inv_rev a b

-- 6ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by simp

-- Lemas usados
-- ============

-- variable (c : G)
-- #check (inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_inv_cancel a : a * a⁻¹ = 1)
-- #check (mul_inv_rev a b : (a * b)⁻¹ = b⁻¹ * a⁻¹)
-- #check (one_mul a : 1 * a = a)
