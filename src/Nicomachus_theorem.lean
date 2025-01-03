-- Nicomachus_theorem.lean
-- Nicomachus’s theorem.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, January 3, 2025
-- =====================================================================

-- ---------------------------------------------------------------------
-- Prove the [Nicomachus's theorem](https://tinyurl.com/gvamrds) which
-- states that the sum of the cubes of the first n natural numbers is
-- equal to the square of the sum of the first n natural numbers; that
-- is, for any natural number n we have
--    1³ + 2³ + ... + n³ = (1 + 2 + ... + n)²
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- It is a consequence of the formulas for the sum of the first n
-- natural numbers and the sum of the cubes of the first n natural
-- numbers; that is,
--    Lemma 1: 1 + 2 + ... + n = n(n+1)/2
--    Lemma 2: 1³ + 2³ + ... + n³ = (n(n+1))²/4
-- In fact,
--    1³ + 2³ + ... + n³ = (n(n+1))²/4               [by Lemma 2]
--                       = (2(1 + 2 + ... + n)²/4    [by Lemma 1]
--                       = (1 + 2 + ... + n)²
--
-- Lemma 1 is equivalent to
--    2(1 + 2 + ... + n) = n(n+1)
-- which is proved by induction:
--
-- Base case: For n = 0, the sum is 0 and
--    2·0 = 0(0+1)
-- Inductive step: Assume the inductive hypothesis:
--    2(1 + 2 + ... + n) = n(n+1)                                    (IH)
-- Then,
--    2(1 + 2 + ... + n + (n+1))
--    = 2(1 + 2 + ... + n) + 2(n+1)
--    = n(n+1) + 2(n+1)                [by IH]
--    = (n+2)(n+1)
--    = (n+1)((n+1)+1)
--
-- Lemma 2 is equivalent to
--    4(1³ + 2³ + ... + n³) = (n(n+1))²
-- which is proved by induction:
--
-- Base case: For n = 0, the sum is 0 and
--    4·0 = (0(0+1))²
-- Inductive step: Assume the inductive hypothesis:
--    4(1³ + 2³ + ... + n³) = (n(n+1))²                              (IH)
-- Then,
--    4(1³ + 2³ + ... + n³ + (n+1)³)
--    = 4(1³ + 2³ + ... + n³) + 4(n+1)³
--    = (n(n+1))² + 4(n+1)³
--    = (n+1)²(n² + 4n + 4)
--    = ((n+1)(n+2))²

-- Proofs with Lean4
-- =================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (m n : ℕ)

set_option pp.fieldNotation false

-- (sum n) is the sum of the first n natural numbers.
def sum : ℕ → ℕ
  | 0      => 0
  | succ n => sum n + (n+1)

@[simp]
lemma suma_zero : sum 0 = 0 := rfl

@[simp]
lemma suma_succ : sum (n + 1) = sum n + (n+1) := rfl

-- (sumCubes n) is the sum of the cubes of the first n natural numbers.
@[simp]
def sumCubes : ℕ → ℕ
  | 0   => 0
  | n+1 => sumCubes n + (n+1)^3

-- Lemma 1: 2(1 + 2 + ... + n) = n(n+1)

-- Proof 1 of Lemma 1
-- ==================

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    calc 2 * sum 0
         = 2 * 0       := congrArg (2 * .) suma_zero
       _ = 0           := mul_zero 2
       _ = 0 * (0 + 1) := zero_mul (0 + 1)
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := congrArg (2 * .) (suma_succ n)
       _ = 2 * sum n + 2 * (n + 1)  := mul_add 2 (sum n) (n + 1)
       _ = n * (n + 1) + 2 * (n + 1) := congrArg (. + 2 * (n + 1)) HI
       _ = (n + 2) * (n + 1)         := (add_mul n 2 (n + 1)).symm
       _ = (n + 1) * (n + 2)         := mul_comm (n + 2) (n + 1)

-- Proof 2 of Lemma 1
-- ==================

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    calc 2 * sum 0
         = 2 * 0       := rfl
       _ = 0           := rfl
       _ = 0 * (0 + 1) := rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := rfl
       _ = 2 * sum n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 2) * (n + 1)         := by ring
       _ = (n + 1) * (n + 2)         := by ring

-- Proof 3 of Lemma 1
-- ==================

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := rfl
       _ = 2 * sum n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 1) * (n + 2)         := by ring

-- Proof 4 of Lemma 1
-- ==================

lemma sum_formula :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero => rfl
  | succ n HI => unfold sum ; linarith [HI]

-- Lemma 2: 4(1³ + 2³ + ... + n³) = (n(n+1))²

-- Proof 1 of Lemma 2
-- ==================

example :
  4 * sumCubes n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumCubes 0 = (0 * (0 + 1)) ^ 2
    calc 4 * sumCubes 0
         = 4 * 0             := by simp only [sumCubes]
       _ = (0 * (0 + 1)) ^ 2 := by simp
  | succ m HI =>
     -- m : ℕ
     -- HI : 4 * sumCubes m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumCubes (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumCubes (m + 1)
         = 4 * (sumCubes m + (m+1)^3)
           := by simp only [sumCubes]
       _ = 4 * sumCubes m + 4*(m+1)^3
           := by ring
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = (m+1)^2*(m^2+4*m+4)
           := by ring
       _ = (m+1)^2*(m+2)^2
           := by ring
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1))^2
           := by simp

-- Proof 2 of Lemma 2
-- ==================

lemma sumCubes_formula :
  4 * sumCubes n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    simp
  | succ m HI =>
    calc 4 * sumCubes (m+1)
         = 4 * sumCubes m + 4*(m+1)^3
           := by {simp ; ring_nf}
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1)) ^ 2
           := by simp

-- Nicomachus's theorem
example :
  sumCubes n = (sum n)^2 :=
by
  have h1 : 4 * sumCubes n = 4 * (sum n)^2 :=
    calc 4 * sumCubes n
       = (n*(n+1))^2    := by simp only [sumCubes_formula]
     _ = (2 * sum n)^2 := by simp only [sum_formula]
     _ = 4 * (sum n)^2 := by ring
  linarith

-- Used lemmas
-- ===========

-- variable (a b c : ℕ)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_zero a : a * 0 = 0)
-- #check (zero_mul a : 0 * a = 0)
