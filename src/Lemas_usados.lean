-- Lemas_usados.lean
-- Lemas usados.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-agosto-2023
-- ---------------------------------------------------------------------

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic

-- Números reales
-- ==============

section reales
variable (a b c : ℝ)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_trans : a < b → b < c → a < c)
#check (mul_comm a b : a * b = b * a)
#check (mul_neg a b : a * -b = -(a * b))
#check (mul_sub a b c : a * (b - c) = a * b - a * c)
#check (neg_add_self a : -a + a = 0)
#check (pow_two a : a ^ 2 = a * a)
#check (two_mul a : 2 * a = a + a)
end reales

-- Anillos
-- =======

section anillos
variable {R : Type _} [Ring R]
variable (a b c : R)
#check (add_assoc a b c : (a + b) + c = a + (b + c))
#check (add_comm a b : a + b = b + a)
#check (add_eq_zero_iff_eq_neg : a + b = 0 ↔ a = -b)
#check (add_left_cancel : a + b = a + c → b = c)
#check (add_left_neg a : -a + a = 0)
#check (add_mul a b c : (a + b) * c = a * c + b * c)
#check (add_neg_cancel_right a b : (a + b) + -b = a)
#check (add_neg_self a : a + -a = 0)
#check (add_right_cancel : a + b = c + b → a = c)
#check (add_right_neg a : a + -a = 0)
#check (add_zero a : a + 0 = a)
#check (mul_add a b c : a * (b + c) = a * b + a * c)
#check (mul_zero a : a * 0 = 0)
#check (neg_add_cancel_left a b : -a + (a + b) = b)
#check (neg_eq_iff_add_eq_zero : -a = b ↔ a + b = 0)
#check (neg_eq_of_add_eq_zero_left : a + b = 0 → -b = a)
#check (neg_eq_of_add_eq_zero_right : a + b = 0 → -a = b)
#check (neg_neg a : -(-a) = a)
#check (neg_zero : -0 = 0)
#check (one_add_one_eq_two : (1 : R) + 1 = 2)
#check (sub_eq_add_neg a b : a - b = a + -b)
#check (sub_self a : a - a = 0)
#check (two_mul a : 2 * a = a + a)
#check (zero_add a : 0 + a = a)
#check (zero_mul a : 0 * a = 0)
end anillos

-- Grupos
-- ======

section grupos
variable {G : Type _} [Group G]
variable (a b c : G)
#check (inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b)
#check (mul_assoc a b c : (a * b) * c = a * (b * c))
#check (mul_inv_self a : a * a⁻¹ = 1)
#check (mul_inv_rev a b : (a * b)⁻¹ = b⁻¹ * a⁻¹)
#check (mul_left_inv a : a⁻¹  * a = 1)
#check (mul_one a : a * 1 = a)
#check (mul_right_inv a : a * a⁻¹ = 1)
#check (one_mul a : 1 * a = a)
end grupos
