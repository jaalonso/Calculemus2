-- Inverso_del_inverso_en_grupos.lean
-- Si G un grupo y a ∈ G, entonces (a⁻¹)⁻¹ = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si G un grupo y a ∈ G, entonces
--    (a⁻¹)⁻¹ = a
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    (a⁻¹)⁻¹ = (a⁻¹)⁻¹·1          [porque 1 es neutro]
--            = (a⁻¹)⁻¹·(a⁻¹·a)    [porque a⁻¹ es el inverso de a]
--            = ((a⁻¹)⁻¹·a⁻¹)·a    [por la asociativa]
--            = 1·a                [porque (a⁻¹)⁻¹ es el inverso de a⁻¹]
--            = a                  [porque 1 es neutro]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a : G}

-- 1ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         := (mul_one (a⁻¹)⁻¹).symm
   _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := congrArg ((a⁻¹)⁻¹ * .) (inv_mul_cancel a).symm
   _ = ((a⁻¹)⁻¹ * a⁻¹) * a := (mul_assoc _ _ _).symm
   _ = 1 * a               := congrArg (. * a) (inv_mul_cancel a⁻¹)
   _ = a                   := one_mul a

-- 2ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         := by simp only [mul_one]
   _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := by simp only [inv_mul_cancel]
   _ = ((a⁻¹)⁻¹ * a⁻¹) * a := by simp only [mul_assoc]
   _ = 1 * a               := by simp only [inv_mul_cancel]
   _ = a                   := by simp only [one_mul]

-- 3ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         := by simp
   _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := by simp
   _ = ((a⁻¹)⁻¹ * a⁻¹) * a := by simp
   _ = 1 * a               := by simp
   _ = a                   := by simp

-- 4ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
by
  apply mul_eq_one_iff_inv_eq.mp
  -- ⊢ a⁻¹ * a = 1
  exact inv_mul_cancel a

-- 5ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
mul_eq_one_iff_inv_eq.mp (inv_mul_cancel a)

-- 6ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
inv_inv a

-- 7ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
by simp

-- Lemas usados
-- ============

-- variable (b c : G)
-- #check (inv_inv a : (a⁻¹)⁻¹ = a)
-- #check (inv_mul_cancel a : a⁻¹  * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b)
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
