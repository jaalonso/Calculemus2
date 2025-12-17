-- Limits_are_less_than_or_equal_to_upper_bounds.lean
-- If x is the limit of u and y is an upper bound of u, then x ≤ y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 3, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean4, we can define that a is the limit of the sequence u by:
--    def is_limit (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
-- and that a is an upper bound of u by:
--    def is_upper_bound (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ n, u n ≤ a
--
-- Prove that if x is the limit of the sequence u and y is an upper
-- bound of u, then x ≤ y.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let us consider the property from the previous exercise, which states
-- that for all x, y ∈ ℝ:
--    (∀ ε > 0, y ≤ x + ε) → y ≤ x
--
-- To prove x ≤ y, it suffices to show that:
--    ∀ ε > 0, x ≤ y + ε
--
-- Let ε > 0. Since x is the limit of the sequence u, there exists a k ∈ ℕ
-- such that:
--    ∀ n ≥ k, |u(n) - x| < ε
-- In particular, we have:
--    |u(k) - x| < ε
-- from which it follows that
--    -ε < u(k) - x
-- and rearranging gives us
--    x < u(k) + ε                                                   (1)
--
-- Since y is an upper bound of u, it follows that:
--    u(k) < y                                                       (2)
--
-- Combining (1) and (2), we obtain
--    x < y + ε
-- which completes the proof.

-- Proofs with Lean4
-- =================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  (u : ℕ → ℝ)
variable (x y : ℝ)

def is_limit (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def is_upper_bound (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

-- Proof 1
-- =======

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  replace hk : -ε < u k - x := neg_lt_of_abs_lt hk
  replace hk : x < u k + ε := neg_lt_sub_iff_lt_add'.mp hk
  apply le_of_lt
  -- ⊢ x < y + ε
  exact lt_add_of_lt_add_right hk (hy k)

-- Proof 2
-- =======

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  apply le_of_lt
  -- ⊢ x < y + ε
  calc x < u k + ε := neg_lt_sub_iff_lt_add'.mp (neg_lt_of_abs_lt hk)
       _ ≤ y + ε   := add_le_add_left (hy k) ε

-- Proof 3
-- =======

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (by linarith)
  rw [abs_lt] at hk
  -- hk : -ε < u k - x ∧ u k - x < ε
  linarith [hy k]

-- Used lemmas
-- ===========

variable (n : ℕ)
variable (a b c d : ℝ)
#check (add_le_add_left : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
#check (le_of_forall_pos_le_add : (∀ ε > 0, y ≤ x + ε) → y ≤ x)
#check (le_of_lt : a < b → a ≤ b)
#check (le_refl n : n ≤ n)
#check (lt_add_of_lt_add_right : a < b + c → b ≤ d → a < d + c)
#check (neg_lt_of_abs_lt : |a| < b → -b < a)
#check (neg_lt_sub_iff_lt_add' : -b < a - c ↔ c < a + b)
