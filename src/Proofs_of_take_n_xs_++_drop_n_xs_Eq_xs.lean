-- Proofs_of_take_n_xs_++_drop_n_xs_Eq_xs.lean
-- Proofs of take n xs ++ drop n xs = xs
-- José A. Alonso Jiménez https://jaalonso.github.io
-- Seville, August 14, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean4, the functions
--    take : Nat → List α → Nat
--    drop : Nat → List α → Nat
--    (++) : List α → List α → List α
-- are defined such that
-- + (take n xs) is the list formed by the first n elements of
--   xs. For example,
--      take 2 [3,5,1,9,7] = [3,5]
-- + (drop n xs) is the list formed by removing the first n elements
--   of xs. For example,
--      drop 2 [3,5,1,9,7] = [1,9,7]
-- + (xs ++ ys) is the list obtained by concatenating xs and ys. For example,
--      [3,5] ++ [1,9,7] = [3,5,1,9,7]
--
-- These functions are characterized by the following lemmas:
--    take_zero      : take 0 xs = []
--    take_nil       : take n [] = []
--    take_cons      : take (succ n) (x :: xs) = x :: take n xs
--    drop_zero      : drop 0 xs = xs
--    drop_nil       : drop n [] = []
--    drop_succ_cons : drop (n + 1) (x :: xs) = drop n xs
--    nil_append     : [] ++ ys = ys
--    cons_append    : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- Prove that
--    take n xs ++ drop n xs = xs
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- We have to prove that
--    (∀ n)(∀ xs)[take n xs ++ drop n xs = xs]
-- We will do it by induction on n.
--
-- Base case: Let n = 0. We have to prove that
--    (∀ xs)[take n xs ++ drop n xs = xs]
-- Let xs be any list. Then
--    take n xs ++ drop n xs = take 0 xs ++ drop 0 xs
--                           = [] ++ xs
--                           = xs
--
-- Inductive step: Assume the inductive hypothesis (IH):
--    (∀ xs)[take n xs ++ drop n xs = xs]
-- and we have to prove that
--    (∀ xs)[take (n+1) xs ++ drop (n+1) xs = xs]
-- We will prove it by cases on xs.
--
-- First case: Assume that xs = []. Then,
--    take (n+1) xs ++ drop (n+1) xs = take (n+1) [] ++ drop (n+1) []
--                                   = [] ++ []
--                                   = []
--
-- Second case: Assume that xs = y :: ys. Then,
--    take (n+1) xs ++ drop (n+1) xs
--    = take (n+1) (y :: ys) ++ drop (n+1) (y :: ys)
--    = (y :: take n ys) ++ drop n ys
--    = y :: (take n ys ++ drop n ys)
--    = y :: ys                                          [por la IH]
--    = xs
--
-- Another alternative way to prove it is by distinguishing the three cases
-- of the definition of take; which is
--    take n xs = [],             if n = 0
--              = [],             if n = m+1 and xs = []
--              = y :: take m ys, if n = m+1 and xs = y :: ys
--
-- Case 1: Assume that n = 0. Then,
--    take n xs ++ drop n xs = take 0 xs ++ drop 0 xs
--                           = [] ++ xs
--                           = xs
--
-- Case 2: Assume that n = m+1 and xs = []. Then,
--    take (m+1) xs ++ drop (m+1) xs = take (m+1) [] ++ drop (m+1) []
--                                   = [] ++ []
--                                   = []
--
-- Case 3: Assume that n = m+1 and xs = y :: ys. Then,
--    take (m+1) xs ++ drop (m+1) xs
--    = take (m+1) (y :: ys) ++ drop (m+1) (y :: ys)
--    = (y :: take m ys) ++ drop m ys
--    = y :: (take m ys ++ drop m ys)
--    = y :: ys                       [by the Lemma applied to m and ys]
--    = xs

-- Proofs with Lean4
-- =================

import Mathlib.Data.List.Basic
import Mathlib.Tactic
open List Nat

variable {α : Type}
variable (n : ℕ)
variable (x : α)
variable (xs : List α)

-- Proof 1
-- =======

example : take n xs ++ drop n xs = xs :=
by
  induction' n with n IH generalizing xs
  . -- ⊢ take zero xs ++ drop zero xs = xs
    calc take zero xs ++ drop zero xs
           = [] ++ xs                 := rfl
         _ = xs                       := rfl
  . -- n : ℕ
    -- IH : ∀ (xs : List α), take n xs ++ drop n xs = xs
    -- xs : List α
    -- ⊢ take (succ n) xs ++ drop (succ n) xs = xs
    cases' xs with y ys
    . -- ⊢ take (succ n) [] ++ drop (succ n) [] = []
      calc take (succ n) [] ++ drop (succ n) []
             = [] ++ [] := rfl
           _ = []       := by rfl
    . -- y : α
      -- ys : List α
      -- ⊢ take (n+1) (y :: ys) ++ drop (n+1) (y :: ys) = y :: ys
      calc
        take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
          = (y :: take n ys) ++ drop n ys := rfl
        _ = y :: (take n ys ++ drop n ys) := rfl
        _ = y :: ys                       := by rw [IH]

-- Proof 2
-- =======

example : take n xs ++ drop n xs = xs :=
by
  induction' n with n IH generalizing xs
  . -- ⊢ take zero xs ++ drop zero xs = xs
    rfl
  . -- n : ℕ
    -- IH : ∀ (xs : List α), take n xs ++ drop n xs = xs
    -- xs : List α
    -- ⊢ take (succ n) xs ++ drop (succ n) xs = xs
    cases' xs with y ys
    . -- ⊢ take (succ n) [] ++ drop (succ n) [] = []
      rfl
    . -- y : α
      -- ys : List α
      -- ⊢ take (n+1) (y :: ys) ++ drop (n+1) (y :: ys) = y :: ys
      calc
        take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
          = y :: (take n ys ++ drop n ys) := rfl
        _ = y :: ys                       := by rw [IH]

-- Proof 3
-- =======

lemma take_drop_1 : ∀ (n : Nat) (xs : List α), take n xs ++ drop n xs = xs
  | 0, xs =>
    -- ⊢ take 0 xs ++ drop 0 xs = xs
    calc
      take 0 xs ++ drop 0 xs
        = [] ++ xs := rfl
      _ = xs       := rfl
  | n+1, [] =>
    -- ⊢ take (n + 1) [] ++ drop (n + 1) [] = []
    calc
      take (n+1) [] ++ drop (n+1) []
        = [] ++ [] := rfl
      _ = []       := by rfl
  | n+1, y :: ys =>
    -- ⊢ take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys) = y :: ys
    calc
      take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
        = (y :: take n ys) ++ drop n ys := rfl
      _ = y :: (take n ys ++ drop n ys) := rfl
      _ = y :: ys                       := by rw [take_drop_1 n ys]

-- Proof 4
-- =======

lemma take_drop_2 : ∀ (n : Nat) (xs : List α), take n xs ++ drop n xs = xs
  | 0, _ =>
    -- ⊢ take 0 xs ++ drop 0 xs = xs
    rfl
  | _+1, [] =>
    -- ⊢ take (n + 1) [] ++ drop (n + 1) [] = []
    rfl
  | n+1, y :: ys =>
    -- ⊢ take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys) = y :: ys
    calc
      take (n + 1) (y :: ys) ++ drop (n + 1) (y :: ys)
      _ = y :: (take n ys ++ drop n ys) := rfl
      _ = y :: ys                       := by rw [take_drop_2 n ys]

-- Proof 5
-- =======

lemma take_drop_3 : take n xs ++ drop n xs = xs :=
take_append_drop n xs
