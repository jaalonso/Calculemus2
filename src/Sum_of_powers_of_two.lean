-- Sum_of_powers_of_two.lean
-- Proofs of ∑k<n. 2^k = 2^n-1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, September 24, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove that
--    1 + 2 + 2² + 2³ + ... + 2⁽ⁿ⁻¹⁾ = 2ⁿ - 1
-- ---------------------------------------------------------------------

-- Proof in natural language
-- ==========================

-- By induction on n.
--
-- Base case: Let n = 0. Then,
--    ∑k<0. 2^k = 0
--              = 2^0 - 1
--              = 2^n - 1
--
-- Induction step: Let n = m+1 and suppose the induction hypothesis
-- (IH)
--    ∑k<m. 2^k = 2^m - 1
-- Then,
--    ∑k<n. 2^k = ∑k<(m+1). 2^k
--              = ∑k<m. 2^k + 2^m
--              = (2^m - 1) + 2^m    [by IH]
--              = (2^m + 2^m) - 1
--              = 2^(m + 1) - 1
--              = 2^n - 1

-- Proofs with Lean4
-- =================

import Mathlib.Tactic

open Finset Nat

variable (n : ℕ)

-- Proof 1
-- =======

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by
  induction n with
  | zero =>
    -- ⊢ ∑ k ∈ range 0, 2 ^ k = 2 ^ 0 - 1
    calc ∑ k ∈ range 0, 2 ^ k
         = 0                   := sum_range_zero (2 ^ .)
       _ = 2 ^ 0 - 1           := by omega
  | succ m HI =>
    -- m : ℕ
    -- HI : ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1
    -- ⊢ ∑ k ∈ range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1
    have h1 : (2^m - 1) + 2^m = (2^m + 2^m) - 1 := by
      have h2 : 2^m ≥ 1 := Nat.one_le_two_pow
      omega
    calc ∑ k in range (m + 1), 2^k
       = ∑ k in range m, (2^k) + 2^m
           := sum_range_succ (2 ^ .) m
     _ = (2^m - 1) + 2^m
           := congrArg (. + 2^m) HI
     _ = (2^m + 2^m) - 1
           := h1
     _ = 2^(m + 1) - 1
           := congrArg (. - 1) (two_pow_succ m).symm

-- Proof 2
-- =======

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
by
  induction n with
  | zero =>
    -- ⊢ ∑ k ∈ range 0, 2 ^ k = 2 ^ 0 - 1
    simp
  | succ m HI =>
    -- m : ℕ
    -- HI : ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1
    -- ⊢ ∑ k ∈ range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1
    have h1 : (2^m - 1) + 2^m = (2^m + 2^m) - 1 := by
      have h2 : 2^m ≥ 1 := Nat.one_le_two_pow
      omega
    calc ∑ k in range (m + 1), 2^k
       = ∑ k in range m, (2^k) + 2^m := sum_range_succ (2 ^ .) m
     _ = (2^m - 1) + 2^m             := by linarith
     _ = (2^m + 2^m) - 1             := h1
     _ = 2^(m + 1) - 1               := by omega

-- Used lemmas
-- ===========

-- variable (f : ℕ → ℕ)
-- #check (Nat.one_le_two_pow : 1 ≤ 2 ^ n)
-- #check (Nat.two_pow_succ n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n)
-- #check (sum_range_succ f n : ∑ x ∈ range (n+1), f x = ∑ x ∈ range n, f x + f n)
-- #check (sum_range_zero f : ∑ k ∈ range 0, f k = 0)
