-- Sum_of_arithmetic_progression.lean
-- Proofs of a+(a+d)+(a+2d)+···+(a+nd)=(n+1)(2a+nd)/2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 7, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove that the sum of the terms of the arithmetic progression
--    a + (a + d) + (a + 2 × d) + ··· + (a + n × d)
-- is (n + 1) × (2 × a + n × d) / 2.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let
--    s(a,d,n) = a + (a + d) + (a + 2d) + ··· + (a + nd)
-- We need to prove that
--    s(a,d,n) = (n + 1)(2a + nd) / 2
-- or, equivalently that
--    2s(a,d,n) = (n + 1)(2a + nd)
-- We will do this by induction on n.
--
-- Base case: Let n = 0. Then,
--    2s(a,d,n) = 2s(a,d,0)
--              = 2·a
--              = (0 + 1)(2a + 0.d)
--              = (n + 1)(2a + nd)
--
-- Induction step: Let n = m+1 and assume the induction hypothesis
-- (IH)
--    2s(m) = (m + 1)(2a + md)
-- Then,
--    2s(n) = 2s(m+1)
--          = 2(s(a,d,m) + (a + (m + 1)d))
--          = 2s(a,d,m) + 2(a + (m + 1)d)
--          = ((m + 1)(2a + md)) + 2(a + (m + 1)d) [by IH]
--          = (m + 2)(2a + (m + 1)d)
--          = (n + 1)(2a + nd)

-- Proof with Lean4
-- ================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a d : ℝ)

set_option pp.fieldNotation false

def sumAP : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, d, n + 1 => sumAP a d n + (a + (n + 1) * d)

@[simp]
lemma sumAP_zero :
  sumAP a d 0 = a :=
by simp only [sumAP]

@[simp]
lemma sumAP_succ :
  sumAP a d (n + 1) = sumAP a d n + (a + (n + 1) * d) :=
by simp only [sumAP]

-- Proof 1
-- =======

example :
  2 * sumAP a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumAP a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    have h : 2 * sumAP a d 0 = (0 + 1) * (2 * a + 0 * d) :=
      calc 2 * sumAP a d 0
           = 2 * a
               := congrArg (2 * .) (sumAP_zero a d)
         _ = (0 + 1) * (2 * a + 0 * d)
               := by ring_nf
    exact_mod_cast h
  | succ m IH =>
    -- m : ℕ
    -- IH : 2 * sumAP a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumAP a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumAP a d (succ m)
         = 2 * (sumAP a d m + (a + (m + 1) * d))
           := congrArg (2 * .) (sumAP_succ m a d)
       _ = 2 * sumAP a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) IH
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast

-- Proof 2
-- =======

example :
  2 * sumAP a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumAP a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    simp
  | succ m IH =>
    -- m : ℕ
    -- IH : 2 * sumAP a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumAP a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumAP a d (succ m)
         = 2 * (sumAP a d m + (a + (m + 1) * d))
           := rfl
       _ = 2 * sumAP a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) IH
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast
