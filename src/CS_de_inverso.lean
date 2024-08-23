-- CS_de_inverso.lean
-- Si G es un grupo y a, b ∈ G tales que ab = 1 entonces a⁻¹ = b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si G es un grupo y a, b ∈ G, tales que
--    a * b = 1
-- entonces
--    a⁻¹ = b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se tiene a partir de la siguiente cadena de igualdades
--    a⁻¹ = a⁻¹ * 1           [por producto por uno]
--        = a⁻¹ * (a * b)     [por hipótesis]
--        = (a⁻¹ * a) * b     [por asociativa]
--        = 1 * b             [por producto con inverso]
--        = b                 [por producto por uno]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs

variable {G : Type _} [Group G]
variable (a b : G)

-- 1º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
    _ = a⁻¹ * (a * b) := by rw [h]
    _ = (a⁻¹ * a) * b := by rw [mul_assoc]
    _ = 1 * b         := by rw [inv_mul_cancel]
    _ = b             := by rw [one_mul]

-- 2º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ = a⁻¹ * 1       := by simp
    _ = a⁻¹ * (a * b) := by simp [h]
    _ = (a⁻¹ * a) * b := by simp
    _ = 1 * b         := by simp
    _ = b             := by simp

-- 3º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  a⁻¹ * (a * b) := by simp [h]
    _ =  b             := by simp

-- 4º demostración
example
  (h : a * b = 1)
  : a⁻¹ = b :=
by exact inv_eq_of_mul_eq_one_right h

-- Lemas usados
-- ============

-- variable (c : G)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (inv_mul_cancel a : a⁻¹  * a = 1)
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
-- #check (inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b)
