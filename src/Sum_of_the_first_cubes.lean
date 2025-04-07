-- Sum_of_the_first_cubes.lean
-- Proofs of 0³+1³+2³+3³+···+n³ = (n(n+1)/2)²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 10, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove that the sum of the first cubes
--    0³ + 1³ + 2³ + 3³ + ··· + n³
-- is (n(n+1)/2)²
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let
--    s(n) = 0³ + 1³ + 2³ + 3³ + ··· + n³
-- We have to prove that
--    s(n) = (n(n+1)/2)²
-- or, equivalently that
--    4s(n) = (n(n+1))²
-- We will do this by induction on n.
--
-- Base case: Let n = 0. Then,
--    4s(n) = 4s(0)
--          = 4·0
--          = 0
--          = (0(0 + 1))^2
--          = (n(n + 1))^2
--
-- Induction step: Let n = m+1 and assume the induction hypothesis
-- (IH)
--    4s(m) = (m(m + 1))^2
-- Entonces,
--    4s(n) = 4s(m+1)
--          = 4(s(m) + (m+1)^3)
--          = 4s(m) + 4(m+1)^3
--          = (m*(m+1))^2 + 4(m+1)^3        [by IH]
--          = (m+1)^2*(m^2+4m+4)
--          = (m+1)^2*(m+2)^2
--          = ((m+1)(m+2))^2
--          = ((m+1)(m+1+1))^2

-- Proofs with Lean4
-- =================

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

set_option pp.fieldNotation false

@[simp]
def sumCubes : ℕ → ℕ
  | 0   => 0
  | n+1 => sumCubes n + (n+1)^3

-- Proof 1
-- =======

example :
  4 * sumCubes n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumCubes 0 = (0 * (0 + 1)) ^ 2
    calc 4 * sumCubes 0
         = 4 * 0             := by simp only [sumCubes]
       _ = (0 * (0 + 1)) ^ 2 := by simp
  | succ m IH =>
     -- m : ℕ
     -- IH : 4 * sumCubes m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumCubes (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumCubes (m + 1)
         = 4 * (sumCubes m + (m+1)^3)
           := by simp only [sumCubes]
       _ = 4 * sumCubes m + 4*(m+1)^3
           := by ring
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) IH
       _ = (m+1)^2*(m^2+4*m+4)
           := by ring
       _ = (m+1)^2*(m+2)^2
           := by ring
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1))^2
           := by simp

-- Proof 2
-- =======

example :
  4 * sumCubes n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumCubes 0 = (0 * (0 + 1)) ^ 2
    simp
  | succ m IH =>
     -- m : ℕ
     -- IH : 4 * sumCubes m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumCubes (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumCubes (m+1)
         = 4 * sumCubes m + 4*(m+1)^3
           := by {simp ; ring_nf}
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) IH
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1)) ^ 2
           := by simp
