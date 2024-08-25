-- Producto_de_potencias_de_la_misma_base_en_monoides.lean
-- Producto_de_potencias_de_la_misma_base_en_monoides
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponentes naturales. En Lean la potencia x^n se
-- se caracteriza por los siguientes lemas:
--    pow_zero : x^0 = 1
--    pow_succ : x^(succ n) = x * x^n
--
-- Demostrar que
--    x^(m + n) = x^m * x^n
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en m.
--
-- Caso base:
--    x^(0 + n) = x^n
--              = 1 * x^n
--              = x^0 * x^n            [por pow_zero]
--
-- Paso: Supongamos que
--    x^(m + n) = x^m * x^n                                         (HI)
-- Entonces
--    x^((m+1) + n) = x^((m + n) + 1)
--                  = x * x^(m + n)    [por pow_succ]
--                  = x * (x^m * x^n)  [por HI]
--                  = (x * x^m) * x^n
--                  = x^(m+1) * x^n    [por pow_succ]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

open Nat

variable {M : Type} [Monoid M]
variable (x : M)
variable (m n : ℕ)

-- 1ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
by
  induction' m with m HI
  . calc x^(0 + n)
       = x^n               := congrArg (x ^ .) (Nat.zero_add n)
     _ = 1 * x^n           := (Monoid.one_mul (x^n)).symm
     _ = x^0 * x^n         := congrArg (. * (x^n)) (pow_zero x).symm
  . calc x^(succ m + n)
       = x^succ (m + n)    := congrArg (x ^.) (succ_add m n)
     _ = x * x^(m + n)     := pow_succ' x (m + n)
     _ = x * (x^m * x^n)   := congrArg (x * .) HI
     _ = (x * x^m) * x^n   := (mul_assoc x (x^m) (x^n)).symm
     _ = x^succ m * x^n    := congrArg (. * x^n) (pow_succ' x m).symm

-- 2ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
by
  induction' m with m HI
  . calc x^(0 + n)
       = x^n             := by simp only [Nat.zero_add]
     _ = 1 * x^n         := by simp only [Monoid.one_mul]
     _ = x^0 * x^n       := by simp only [_root_.pow_zero]
  . calc x^(succ m + n)
       = x^succ (m + n)  := by simp only [succ_add]
     _ = x * x^(m + n)   := by simp only [_root_.pow_succ']
     _ = x * (x^m * x^n) := by simp only [HI]
     _ = (x * x^m) * x^n := (mul_assoc x (x^m) (x^n)).symm
     _ = x^succ m * x^n  := by simp only [_root_.pow_succ']

-- 3ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
by
  induction' m with m HI
  . calc x^(0 + n)
       = x^n             := by simp [Nat.zero_add]
     _ = 1 * x^n         := by simp
     _ = x^0 * x^n       := by simp
  . calc x^(succ m + n)
       = x^succ (m + n)  := by simp [succ_add]
     _ = x * x^(m + n)   := by simp [_root_.pow_succ']
     _ = x * (x^m * x^n) := by simp [HI]
     _ = (x * x^m) * x^n := (mul_assoc x (x^m) (x^n)).symm
     _ = x^succ m * x^n  := by simp [_root_.pow_succ']

-- 4ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
pow_add x m n

-- Lemas usados
-- ============

-- variable (y z : M)
-- #check (Monoid.one_mul x : 1 * x = x)
-- #check (Nat.zero_add n : 0 + n = n)
-- #check (mul_assoc x y z : (x * y) * z = x * (y * z))
-- #check (pow_add x m n : x^(m + n) = x^m * x^n)
-- #check (pow_succ' x n : x ^ succ n = x * x ^ n)
-- #check (pow_zero x : x ^ 0 = 1)
-- #check (succ_add n m : succ n + m = succ (n + m))
