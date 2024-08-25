-- Proofs_of_the_equality_length(xs++ys)_Eq_length(xs)+length(ys).lean
-- Proofs of the equality length(xs ++ ys) = length(xs) + length(ys).
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 7, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean, the functions
--    length : list α → nat
--    (++)   : list α → list α → list α
-- are defined such that
-- + (length xs) is the length of xs. For example,
--      length [2,3,5,3] = 4
-- + (xs ++ ys) is the list obtained by concatenating xs and ys. For
--   example.
--      [1,2] ++ [2,3,5,3] = [1,2,2,3,5,3]
--
-- These functions are characterized by the following lemmas:
--    length_nil  : length [] = 0
--    length_cons : length (x :: xs) = length xs + 1
--    nil_append  : [] ++ ys = ys
--    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)
--
-- To prove that
--    length (xs ++ ys) = length xs + length ys
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- By induction on xs.
--
-- Base case: Suppose that xs = []. Then,
--    length (xs ++ ys) = length ([] ++ ys)
--                      = length ys
--                      = 0 + length ys
--                      = length [] + length ys
--                      = length xs + length ys
--
-- Induction step: Suppose that xs = a :: as and that the induction
-- hypothesis (IH) holds
--    length (as ++ ys) = length as + length ys                     (IH)
-- Then,
--    length (xs ++ ys) = length ((a :: as) ++ ys)
--                      = length (a :: (as ++ ys))
--                      = length (as ++ ys) + 1
--                      = (length as + length ys) + 1      [por IH]
--                      = (length as + 1) + length ys
--                      = length (a :: as) + length ys
--                      = length xs + length ys

-- Proofs with Lean4
-- =================

import Mathlib.Tactic

open List

variable {α : Type}
variable (xs ys : List α)

-- Proof 1
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as IH
  . calc length ([] ++ ys)
         = length ys
           := congr_arg length (nil_append ys)
       _ = 0 + length ys
           := (zero_add (length ys)).symm
       _ = length [] + length ys
           := congrArg (. + length ys) length_nil.symm
  . calc length ((a :: as) ++ ys)
         = length (a :: (as ++ ys))
           := congr_arg length (cons_append a as ys)
       _ = length (as ++ ys) + 1
           := length_cons a (as ++ ys)
       _ = (length as + length ys) + 1
           := congrArg (. + 1) IH
       _ = (length as + 1) + length ys
           := (Nat.succ_add (length as) (length ys)).symm
       _ = length (a :: as) + length ys
           := congrArg (. + length ys) (length_cons a as).symm

-- Proof 2
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as IH
  . calc length ([] ++ ys)
         = length ys
           := by rw [nil_append]
       _ = 0 + length ys
           := (zero_add (length ys)).symm
       _ = length [] + length ys
           := by rw [length_nil]
  . calc length ((a :: as) ++ ys)
         = length (a :: (as ++ ys))
           := by rw [cons_append]
       _ = length (as ++ ys) + 1
           := by rw [length_cons]
       _ = (length as + length ys) + 1
           := by rw [IH]
       _ = (length as + 1) + length ys
           := (Nat.succ_add (length as) (length ys)).symm
       _ = length (a :: as) + length ys
           := congrArg (. + length ys) (length_cons a as).symm

-- Proof 3
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with _ as IH
  . simp only [nil_append, zero_add, length_nil]
  . simp only [cons_append, length_cons, IH, Nat.succ_add]

-- Proof 4
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with _ as IH
  . simp
  . simp [IH, Nat.succ_add]

-- Proof 5
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as IH
  . simp
  . simp [IH] ; linarith

-- Proof 6
-- =======

lemma length_conc_1 (xs ys : List α):
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | nil => calc
    length ([] ++ ys)
        = length ys
          := by rw [nil_append]
      _ = 0 + length ys
          := by rw [zero_add]
      _ = length [] + length ys
          := by rw [length_nil]
  | cons a as IH => calc
    length ((a :: as) ++ ys)
        = length (a :: (as ++ ys))
          := by rw [cons_append]
      _ = length (as ++ ys) + 1
          := by rw [length_cons]
      _ = (length as + length ys) + 1
          := by rw [IH]
      _ = (length as + 1) + length ys
          := (Nat.succ_add (length as) (length ys)).symm
      _ = length (a :: as) + length ys
          := by rw [length_cons]

-- Proof 7
-- =======

lemma length_conc_2 (xs ys : List α):
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | nil          => simp
  | cons _ as IH => simp [IH, Nat.succ_add]

-- Proof 8
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as IH
  . -- ⊢ length ([] ++ ys) = length [] + length ys
    rw [nil_append]
    -- ⊢ length ys = length [] + length ys
    rw [length_nil]
    -- ⊢ length ys = 0 + length ys
    rw [zero_add]
  . -- a : α
    -- as : List α
    -- IH : length (as ++ ys) = length as + length ys
    -- ⊢ length (a :: as ++ ys) = length (a :: as) + length ys
    rw [cons_append]
    -- ⊢ length (a :: (as ++ ys)) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length (as ++ ys)) = length (a :: as) + length ys
    rw [IH]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length as + length ys) = Nat.succ (length as) + length ys
    rw [Nat.succ_add]

-- Proof 9
-- =======

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as IH
  . -- ⊢ length ([] ++ ys) = length [] + length ys
    rw [nil_append]
    -- ⊢ length ys = length [] + length ys
    rw [length_nil]
    -- ⊢ length ys = 0 + length ys
    rw [zero_add]
  . -- a : α
    -- as : List α
    -- IH : length (as ++ ys) = length as + length ys
    -- ⊢ length (a :: as ++ ys) = length (a :: as) + length ys
    rw [cons_append]
    -- ⊢ length (a :: (as ++ ys)) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length (as ++ ys)) = length (a :: as) + length ys
    rw [IH]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [Nat.succ_add]

-- Proof 10
-- ========

example :
  length (xs ++ ys) = length xs + length ys :=
by
  induction' xs with a as IH
  . -- ⊢ length ([] ++ ys) = length [] + length ys
    rw [nil_append]
    -- ⊢ length ys = length [] + length ys
    rw [length_nil]
    -- ⊢ length ys = 0 + length ys
    rw [zero_add]
  . -- a : α
    -- as : List α
    -- IH : length (as ++ ys) = length as + length ys
    -- ⊢ length (a :: as ++ ys) = length (a :: as) + length ys
    rw [cons_append]
    -- ⊢ length (a :: (as ++ ys)) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length (as ++ ys)) = length (a :: as) + length ys
    rw [IH]
    -- ⊢ Nat.succ (length as + length ys) = length (a :: as) + length ys
    rw [length_cons]
    -- ⊢ Nat.succ (length as + length ys) = Nat.succ (length as) + length ys
    linarith

-- Proof 11
-- ========

example :
  length (xs ++ ys) = length xs + length ys :=
length_append xs ys

-- Proof 12
-- ========

example :
  length (xs ++ ys) = length xs + length ys :=
by simp

-- Used lemmas
-- ===========

-- variable (m n p : ℕ)
-- variable (x : α)
-- #check (Nat.succ_add n m : Nat.succ n + m = Nat.succ (n + m))
-- #check (cons_append x xs ys : (x :: xs) ++ ys = x :: (xs ++ ys))
-- #check (length_append xs ys : length (xs ++ ys) = length xs + length ys)
-- #check (length_cons x xs : length (x :: xs) = length xs + 1)
-- #check (length_nil : length [] = 0)
-- #check (nil_append xs : [] ++ xs = xs)
-- #check (zero_add n : 0 + n = n)
