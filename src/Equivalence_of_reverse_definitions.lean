-- Equivalence_of_reverse_definitions.lean
-- Equivalence of reverse definitions.
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 19, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean4, the function
--    reverse : List α → List α
-- is defined such that (reverse xs) is the list obtained by reversing
-- the order of  elements in xs, such that the first element becomes the
-- last, the second element becomes the second to last, and so on,
-- resulting in a new list with the same elements but in the opposite
-- sequence. For example,
--    reverse  [3,2,5,1] = [1,5,2,3]
--
-- Its definition is
--    def reverseAux : List α → List α → List α
--      | [],    ys => ys
--      | x::xs, ys => reverseAux xs (x::ys)
--
--    def reverse (xs : List α) : List α :=
--      reverseAux xs []
--
-- The following lemmas characterize its behavior:
--    reverseAux_nil : reverseAux [] ys = ys
--    reverseAux_cons : reverseAux (x::xs) ys = reverseAux xs (x::ys)
--
-- An alternative definition is
--    def reverse2 : List α → List α
--      | []        => []
--      | (x :: xs) => reverse2 xs ++ [x]
--
-- Prove that the two definitions are equivalent; that is,
--    reverse xs = reverse2 xs
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- It follows from the following auxiliary lemma:
--    (∀ xs, ys)[reverseAux xs ys = (reverse2 xs) ++ ys]
-- Indeed,
--    reverse xs = reverseAux xs []
--               = reverse2 xs ++ []    [by el lema auxiliar]
--               = reverse2 xs
--
-- The auxiliary lemma is proven by induction on xs.
--
-- Base case: Suppose xs = []. Then,
--    reverseAux xs ys = reverseAux [] ys
--                     = ys
--                     = [] ++ ys
--                     = reverse2 [] ++ ys
--                     = reverse2 xs ++ ys
--
-- Induction step: Suppose xs = a::as and the induction hypothesis (IH):
--    (∀ ys)[reverseAux as ys = reverse2 as ++ ys]
-- Then,
--    reverseAux xs ys = reverseAux (a :: as) ys
--                     = reverseAux as (a :: ys)
--                     = reverse2 as ++ (a :: ys)   [by IH]
--                     = reverse2 as ++ ([a] ++ ys)
--                     = (reverse2 as ++ [a]) ++ ys
--                     = reverse2 (a :: as) ++ ys
--                     = reverse2 xs ++ ys

-- Proofs with Lean4
-- =================

import Mathlib.Data.List.Basic

set_option pp.fieldNotation false

open List

variable {α : Type}
variable (x : α)
variable (xs ys : List α)

-- Definition and simplification rules for reverse2
-- ================================================

def reverse2 : List α → List α
  | []        => []
  | (x :: xs) => reverse2 xs ++ [x]

@[simp]
lemma reverse2_nil :
  reverse2 ([] : List α) = [] :=
  rfl

@[simp]
lemma reverse2_cons :
  reverse2 (x :: xs) = reverse2 xs ++ [x] :=
  rfl

-- Auxiliary lemma: reverseAux xs ys = (reverse2 xs) ++ ys
-- =======================================================

-- Proof 1 of the auxiliary lemma
-- ==============================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction xs generalizing ys with
  | nil =>
    -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := reverseAux_nil
       _ = [] ++ ys                   := (nil_append ys).symm
       _ = reverse2 [] ++ ys          := congrArg (. ++ ys) reverse2_nil.symm
  | cons a as IH =>
    -- a : α
    -- as : List α
    -- IH : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := reverseAux_cons
       _ = reverse2 as ++ (a :: ys)   := (IH (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := congrArg (reverse2 as ++ .) singleton_append
       _ = (reverse2 as ++ [a]) ++ ys := (append_assoc (reverse2 as) [a] ys).symm
       _ = reverse2 (a :: as) ++ ys   := congrArg (. ++ ys) (reverse2_cons a as).symm

-- Proof 2 of the auxiliary lemma
-- ==============================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction xs generalizing ys with
  | nil =>
    -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := by rw [reverseAux_nil]
       _ = [] ++ ys                   := by rw [nil_append]
       _ = reverse2 [] ++ ys          := by rw [reverse2_nil]
  | cons a as IH =>
    -- a : α
    -- as : List α
    -- IH : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by rw [reverseAux_cons]
       _ = reverse2 as ++ (a :: ys)   := by rw [(IH (a :: ys))]
       _ = reverse2 as ++ ([a] ++ ys) := by rw [singleton_append]
       _ = (reverse2 as ++ [a]) ++ ys := by rw [append_assoc]
       _ = reverse2 (a :: as) ++ ys   := by rw [reverse2_cons]

-- Proof 3 of the auxiliary lemma
-- ==============================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction xs generalizing ys with
  | nil =>
     -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                := rfl
       _ = [] ++ ys          := by rfl
       _ = reverse2 [] ++ ys := rfl
  | cons a as IH =>
    -- a : α
    -- as : List α
    -- IH : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := rfl
       _ = reverse2 as ++ (a :: ys)   := (IH (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := rfl
       _ = (reverse2 as ++ [a]) ++ ys := by rw [append_assoc]
       _ = reverse2 (a :: as) ++ ys   := rfl

-- Proof 4 of the auxiliary lemma
-- ==============================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction xs generalizing ys with
  | nil =>
    -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := by simp
       _ = [] ++ ys                   := by simp
       _ = reverse2 [] ++ ys          := by simp
  | cons a as IH =>
    -- a : α
    -- as : List α
    -- IH : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by simp
       _ = reverse2 as ++ (a :: ys)   := (IH (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := by simp
       _ = (reverse2 as ++ [a]) ++ ys := by simp
       _ = reverse2 (a :: as) ++ ys   := by simp

-- Proof 5 of the auxiliary lemma
-- ==============================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction xs generalizing ys with
  | nil =>
    -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    simp
  | cons a as IH =>
    -- a : α
    -- as : List α
    -- IH : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by simp
       _ = reverse2 as ++ (a :: ys)   := (IH (a :: ys))
       _ = reverse2 (a :: as) ++ ys   := by simp

-- Proof 6 of the auxiliary lemma
-- ==============================

lemma reverse2_equiv :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction xs generalizing ys with
  | nil =>
    -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    rw [reverseAux_nil]
    -- ⊢ ys = reverse2 [] ++ ys
    rw [reverse2_nil]
    -- ⊢ ys = [] ++ ys
    rw [nil_append]
  | cons a as IH =>
    -- a : α
    -- as : List α
    -- IH : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    rw [reverseAux_cons]
    -- ⊢ reverseAux as (a :: ys) = reverse2 (a :: as) ++ ys
    rw [(IH (a :: ys))]
    -- ⊢ reverse2 as ++ a :: ys = reverse2 (a :: as) ++ ys
    rw [reverse2_cons]
    -- ⊢ reverse2 as ++ a :: ys = (reverse2 as ++ [a]) ++ ys
    rw [append_assoc]
    -- ⊢ reverse2 as ++ a :: ys = reverse2 as ++ ([a] ++ ys)
    rw [singleton_append]

-- Proof of the main lemma
-- ========================

example : reverse xs = reverse2 xs :=
calc reverse xs
     = reverseAux xs []  := rfl
   _ = reverse2 xs ++ [] := by rw [reverse2_equiv]
   _ = reverse2 xs       := by rw [append_nil]

-- Used lemmas
-- ===========

-- variable (ys zs : List α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (append_nil xs : xs ++ [] = xs)
-- #check (nil_append xs : [] ++ xs = xs)
-- #check (reverse xs = reverseAux xs [])
-- #check (reverseAux_cons : reverseAux (x::xs) ys = reverseAux xs (x::ys))
-- #check (reverseAux_nil : reverseAux [] ys = ys)
-- #check (singleton_append : [x] ++ ys = x :: ys)
