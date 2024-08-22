-- Unicidad_de_los_inversos_en_los_grupos.lean
-- Unicidad de los inversos en los grupos
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es un elemento de un grupo G, entonces a tiene un
-- único inverso; es decir, si b es un elemento de G tal que a * b = 1,
-- entonces a⁻¹ = b.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    a⁻¹ = a⁻¹·1        [porque 1 es neutro]
--        = a⁻¹·(a·b)    [por hipótesis]
--        = (a⁻¹·a)·b    [por la asociativa]
--        = 1·b          [porque a⁻¹ es el inverso de a]
--        = b            [porque 1 es neutro]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a b : G}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1  := (mul_one a⁻¹).symm
  _ = a⁻¹ * (a * b) := congrArg (a⁻¹ * .) h.symm
  _ = (a⁻¹ * a) * b := (mul_assoc a⁻¹ a b).symm
  _ = 1 * b         := congrArg (. * b) (inv_mul_cancel a)
  _ = b             := one_mul b

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       := by simp only [mul_one]
       _ = a⁻¹ * (a * b) := by simp only [h]
       _ = (a⁻¹ * a) * b := by simp only [mul_assoc]
       _ = 1 * b         := by simp only [inv_mul_cancel]
       _ = b             := by simp only [one_mul]

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       := by simp
       _ = a⁻¹ * (a * b) := by simp [h]
       _ = (a⁻¹ * a) * b := by simp
       _ = 1 * b         := by simp
       _ = b             := by simp

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * (a * b) := by simp [h]
       _ = b             := by simp

-- 5ª demostración
-- ===============

example
  (h : b * a = 1)
  : b = a⁻¹ :=
eq_inv_iff_mul_eq_one.mpr h

-- Lemas usados
-- ============

-- variable (c : G)
-- #check (eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1)
-- #check (inv_mul_cancel a : a⁻¹ * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
