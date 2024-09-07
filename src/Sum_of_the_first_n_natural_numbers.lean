-- Sum_of_the_first_n_natural_numbers.lean
-- Proofs of "0 + 1 + 2 + 3 + ··· + n = n × (n + 1)/2"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 5, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove that the sum of the natural numbers
--    0 + 1 + 2 + 3 + ··· + n
-- is n × (n + 1)/2
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- Let
--    s(n) = 0 + 1 + 2 + 3 + ··· + n
-- We need to prove that
--    s(n) = n(n + 1)/2
-- or, equivalently, that
--    2s(n) = n(n + 1)
-- We will do this by induction on n.
--
-- Base Case: Let n = 0. Then,
--    2s(n) = 2s(0)
--          = 2·0
--          = 0
--          = 0.(0 + 1)
--          = n.(n + 1)
--
-- Induction Step: Let n = m + 1 and assume the induction hypothesis
-- (IH)
--    2s(m) = m(m+1)
-- Then,
--    2s(n) = 2s(m+1)
--          = 2(s(m) + (m+1))
--          = 2s(m) + 2(m+1)
--          = m(m + 1) + 2(m + 1)    [by IH]
--          = (m + 2)(m + 1)
--          = (m + 1)(m + 2)
--          = n(n+1)

-- Proofs with Lean4
-- =================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

set_option pp.fieldNotation false

def sum : ℕ → ℕ
  | 0      => 0
  | succ n => sum n + (n+1)

@[simp]
lemma sum_zero : sum 0 = 0 := rfl

@[simp]
lemma sum_succ : sum (n + 1) = sum n + (n+1) := rfl

-- Proof 1
-- =======

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    calc 2 * sum 0
         = 2 * 0       := congrArg (2 * .) sum_zero
       _ = 0           := mul_zero 2
       _ = 0 * (0 + 1) := zero_mul (0 + 1)
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := congrArg (2 * .) (sum_succ n)
       _ = 2 * sum n + 2 * (n + 1)  := mul_add 2 (sum n) (n + 1)
       _ = n * (n + 1) + 2 * (n + 1) := congrArg (. + 2 * (n + 1)) HI
       _ = (n + 2) * (n + 1)         := (add_mul n 2 (n + 1)).symm
       _ = (n + 1) * (n + 2)         := mul_comm (n + 2) (n + 1)

-- Proof 2
-- =======

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

-- Proof 3
-- =======

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
         = 2 * (sum n + (n + 1))     := rfl
       _ = 2 * sum n + 2 * (n + 1)   := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 1) * (n + 2)         := by ring

-- Proof 4
-- =======

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero => rfl
  | succ n HI => unfold sum ; linarith [HI]

-- Used lemmas
-- ===========

-- variable (a b c : ℕ)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_zero a : a * 0 = 0)
-- #check (zero_mul a : 0 * a = 0)
