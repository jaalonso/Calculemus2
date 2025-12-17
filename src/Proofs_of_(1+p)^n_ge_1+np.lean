-- Proofs_of_(1+p)^n_ge_1+np.lean
-- Proofs of "If p > -1, then (1+p)ⁿ ≥ 1+np"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 12, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Let p ∈ ℝ and n ∈ ℕ. Prove that if p > -1, then
--    (1 + p)^n ≥ 1 + n*p
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- By induction on n.
--
-- Base case: Let n = 0. Then,
--    (1+p)^n = (1+p)^0
--            = 1
--            ≥ 1
--            = 1 + 0
--            = 1 + 0·p
--            = 1 + n·p
--
-- Induction step: Let n = m+1 and assume the induction hypothesis
-- (IH)
--    (1 + p)^m ≥ 1 + mp
-- Then,
--    (1 + p)^n = (1 + p)^(m+1)
--              = (1 + p)^m(1 + p)
--              ≥ (1 + m * p)(1 + p)    [by IH]
--              = (1 + p + mp) + m(pp)
--              ≥ 1 + p + mp
--              = 1 + (m + 1)p
--              = 1 + np

-- Proof with Lean4
-- ================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

variable (p : ℝ)
variable (n : ℕ)

-- Proof 1
-- =======

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
by
  induction n with
  | zero =>
    -- ⊢ (1 + p) ^ 0 ≥ 1 + ↑0 * p
    have h1 : (1 + p) ^ 0 ≥ 1 + 0 * p :=
      calc (1 + p) ^ 0
           = 1           := pow_zero (1 + p)
         _ ≥ 1           := le_refl 1
         _ = 1 + 0       := (add_zero 1).symm
         _ = 1 + 0 * p   := congrArg (1 + .) (zero_mul p).symm
    exact_mod_cast h1
  | succ m IH =>
    -- m : ℕ
    -- IH : (1 + p) ^ m ≥ 1 + ↑m * p
    -- ⊢ (1 + p) ^ (m + 1) ≥ 1 + ↑(m + 1) * p
    have h1 : 1 + p > 0 := neg_lt_iff_pos_add'.mp h
    have h2 : p*p ≥ 0 := mul_self_nonneg p
    replace h2 : ↑m*(p*p) ≥ 0 := mul_nonneg (cast_nonneg m) h2
    calc (1 + p)^(m+1)
         = (1 + p)^m * (1 + p)
             := pow_succ (1 + p) m
       _ ≥ (1 + m * p) * (1 + p)
             := (mul_le_mul_iff_of_pos_right h1).mpr IH
       _ = (1 + p + m*p) + m*(p*p)
             := by ring
       _ ≥ 1 + p + m*p
             := le_add_of_nonneg_right h2
       _ = 1 + (m + 1) * p
             := by ring
       _ = 1 + ↑(m+1) * p
             := by norm_num

-- Proof 2
-- =======

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
by
  induction n with
  | zero =>
    -- ⊢ (1 + p) ^ 0 ≥ 1 + ↑0 * p
    simp
  | succ m IH =>
    -- m : ℕ
    -- IH : (1 + p) ^ m ≥ 1 + ↑m * p
    -- ⊢ (1 + p) ^ (m + 1) ≥ 1 + ↑(m + 1) * p
    calc (1 + p)^(m+1)
         = (1 + p)^m * (1 + p)     := by rfl
       _ ≥ (1 + m * p) * (1 + p)   := by nlinarith
       _ = (1 + p + m*p) + m*(p*p) := by ring
       _ ≥ 1 + p + m*p             := by nlinarith
       _ = 1 + (m + 1) * p         := by ring
       _ = 1 + ↑(m+1) * p          := by norm_num

-- Used lemmas
-- ===========

variable (a b c : ℝ)
#check (add_zero a : a + 0 = a)
#check (cast_nonneg n : 0 ≤ ↑n)
#check (le_add_of_nonneg_right : 0 ≤ b → a ≤ a + b)
#check (le_refl a : a ≤ a)
#check (mul_le_mul_iff_of_pos_right : 0 < a → (b * a ≤ c * a ↔ b ≤ c))
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
#check (mul_self_nonneg a : 0 ≤ a * a)
#check (neg_lt_iff_pos_add' : -a < b ↔ 0 < a + b)
#check (pow_succ a n : a ^ (n + 1) = a ^ n * a)
#check (pow_zero a : a ^ 0 = 1)
#check (zero_mul a : 0 * a = 0)
