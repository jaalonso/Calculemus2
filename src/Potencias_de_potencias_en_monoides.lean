-- Potencias_de_potencias_en_monoides.lean
-- Si M es un monoide, a ∈ M y m, n ∈ ℕ, entonces a^(m·n) = (a^m)^n
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponentes naturales. En Lean4, la potencia x^n se
-- se caracteriza por los siguientes lemas:
--    pow_zero : x^0 = 1
--    pow_succ' : x^(succ n) = x * x^n
--
-- Demostrar que si M es un monoide, a ∈ M y m, n ∈ ℕ, entonces
--    a^(m·n) = (a^m)^n
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en n.
--
-- Caso base: Supongamos que n = 0. Entonces,
--    a^(m·0) = a^0
--            = 1         [por pow_zero]
--            = (a^m)^0   [por pow_zero]
--
-- Paso de indución: Supogamos que se verifica para n; es decir,
--    a^(m·n) = (a^m)^n
-- Entonces,
--    a^(m·(n+1)) = a^(m·n + m)
--                = a^(m·n)·a^m
--                = (a^m)^n·a^m    [por HI]
--                = (a^m)^(n+1)    [por pow_succ']

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

open Nat

variable {M : Type} [Monoid M]
variable (a : M)
variable (m n : ℕ)

-- 1ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . calc a^(m * 0)
         = a^0             := congrArg (a ^ .) (Nat.mul_zero m)
       _ = 1               := pow_zero a
       _ = (a^m)^0         := (pow_zero (a^m)).symm
  . calc a^(m * succ n)
         = a^(m * n + m)   := congrArg (a ^ .) (Nat.mul_succ m n)
       _ = a^(m * n) * a^m := pow_add a (m * n) m
       _ = (a^m)^n * a^m   := congrArg (. * a^m) HI
       _ = (a^m)^(succ n)  := (pow_succ (a^m) n).symm

-- 2ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . calc a^(m * 0)
         = a^0             := by simp only [Nat.mul_zero]
       _ = 1               := by simp only [_root_.pow_zero]
       _ = (a^m)^0         := by simp only [_root_.pow_zero]
  . calc a^(m * succ n)
         = a^(m * n + m)   := by simp only [Nat.mul_succ]
       _ = a^(m * n) * a^m := by simp only [pow_add]
       _ = (a^m)^n * a^m   := by simp only [HI]
       _ = (a^m)^succ n    := by simp only [_root_.pow_succ]

-- 3ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . calc a^(m * 0)
         = a^0             := by simp [Nat.mul_zero]
       _ = 1               := by simp
       _ = (a^m)^0         := by simp
  . calc a^(m * succ n)
         = a^(m * n + m)   := by simp [Nat.mul_succ]
       _ = a^(m * n) * a^m := by simp [pow_add]
       _ = (a^m)^n * a^m   := by simp [HI]
       _ = (a^m)^succ n    := by simp [_root_.pow_succ]

-- 4ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . simp [Nat.mul_zero]
  . simp [Nat.mul_succ,
          pow_add,
          HI,
          _root_.pow_succ]

-- 5ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . -- ⊢ a ^ (m * 0) = (a ^ m) ^ 0
    rw [Nat.mul_zero]
    -- ⊢ a ^ 0 = (a ^ m) ^ 0
    rw [_root_.pow_zero]
    -- ⊢ 1 = (a ^ m) ^ 0
    rw [_root_.pow_zero]
  . -- n : ℕ
    -- HI : a ^ (m * n) = (a ^ m) ^ n
    -- ⊢ a ^ (m * (n + 1)) = (a ^ m) ^ (n + 1)
    rw [Nat.mul_succ]
    -- ⊢ a ^ (m * n + m) = (a ^ m) ^ (n + 1)
    rw [pow_add]
    -- ⊢ a ^ (m * n) * a ^ m = (a ^ m) ^ (n + 1)
    rw [HI]
    -- ⊢ (a ^ m) ^ n * a ^ m = (a ^ m) ^ (n + 1)
    rw [_root_.pow_succ]

-- 6ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . rw [Nat.mul_zero, _root_.pow_zero, _root_.pow_zero]
  . rw [Nat.mul_succ, pow_add, HI, _root_.pow_succ]

-- 7ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
pow_mul a m n

-- Lemas usados
-- ============

-- #check (Nat.mul_succ n m : n * succ m = n * m + n)
-- #check (Nat.mul_zero m : m * 0 = 0)
-- #check (pow_add a m n : a ^ (m + n) = a ^ m * a ^ n)
-- #check (pow_mul a m n : a ^ (m * n) = (a ^ m) ^ n)
-- #check (pow_succ a n : a ^ (n + 1) = a ^ n * a)
-- #check (pow_zero a : a ^ 0 = 1)
