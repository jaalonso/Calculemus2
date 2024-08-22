-- Propiedad_cancelativa_en_grupos.lean
-- Si G es un grupo y a, b, c ∈ G tales que a·b = a·c, entonces b = c.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea G un grupo y a,b,c ∈ G. Demostrar que si a·b = a·c, entonces
-- b = c.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    b = 1·b          [porque 1 es neutro]
--      = (a⁻¹·a)·b    [porque a⁻¹ es el inverso de a]
--      = a⁻¹·(a·b)    [por la asociativa]
--      = a⁻¹·(a·c)    [por la hipótesis]
--      = (a⁻¹·a)·c    [por la asociativa]
--      = 1·c          [porque a⁻¹ es el inverso de a]
--      = c            [porque 1 es neutro]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a b c : G}

-- 1ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         := (one_mul b).symm
     _ = (a⁻¹ * a) * b := congrArg (. * b) (inv_mul_cancel a).symm
     _ = a⁻¹ * (a * b) := mul_assoc a⁻¹ a b
     _ = a⁻¹ * (a * c) := congrArg (a⁻¹ * .) h
     _ = (a⁻¹ * a) * c := (mul_assoc a⁻¹ a c).symm
     _ = 1 * c         := congrArg (. * c) (inv_mul_cancel a)
     _ = c             := one_mul c

-- 2ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         := by rw [one_mul]
     _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
     _ = a⁻¹ * (a * b) := by rw [mul_assoc]
     _ = a⁻¹ * (a * c) := by rw [h]
     _ = (a⁻¹ * a) * c := by rw [mul_assoc]
     _ = 1 * c         := by rw [inv_mul_cancel]
     _ = c             := by rw [one_mul]

-- 3ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         := by simp
     _ = (a⁻¹ * a) * b := by simp
     _ = a⁻¹ * (a * b) := by simp
     _ = a⁻¹ * (a * c) := by simp [h]
     _ = (a⁻¹ * a) * c := by simp
     _ = 1 * c         := by simp
     _ = c             := by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = a⁻¹ * (a * b) := by simp
     _ = a⁻¹ * (a * c) := by simp [h]
     _ = c             := by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
mul_left_cancel h

-- 5ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
by aesop

-- Lemas usados
-- ============

-- #check (inv_mul_cancel a : a⁻¹ * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_left_cancel : a * b = a * c → b = c)
-- #check (one_mul a : 1 * a = a)
