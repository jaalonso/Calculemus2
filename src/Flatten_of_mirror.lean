-- Flatten_of_mirror.lean
-- Proofs of "flatten (mirror a) = reverse (flatten a)"
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 28, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- The tree corresponding to
--        3
--       / \
--      2   4
--     / \
--    1   5
-- can be represented by the term
--    Node 3 (Node 2 (Leaf 1) (Leaf 5)) (Leaf 4)
-- using the datatype defined by
--    inductive Tree' (α : Type) : Type
--      | Leaf : α → Tree' α
--      | Node : α → Tree' α → Tree' α → Tree' α
--
-- The mirror image of the previous tree is
--      3
--     / \
--    4   2
--       / \
--      5   1
-- and the list obtained by flattening it (traversing it in infix order)
-- is
--    [4, 3, 5, 2, 1]
--
-- The definition of the function that calculates the mirror image is
--    def mirror : Tree' α → Tree' α
--      | Leaf x     => Leaf x
--      | Node x l r => Node x (mirror r) (mirror l)
-- and the one that flattens the tree is
--    def flatten : Tree' α → List α
--      | Leaf x     => [x]
--      | Node x l r => (flatten l) ++ [x] ++ (flatten r)
--
-- Prove that
--    flatten (mirror a) = reverse (flatten a)
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- From the definition of the mirror function, we have the following
-- lemmas
--    mirror1  : mirror (Leaf x) = Leaf x
--    mirror2  : mirror (Node x l r) = Node x (mirror r) (mirror l)
--    flatten1 : flatten (Leaf x) = [x]
--    flatten2 : flatten (Node x l r) = (flatten l) ++ [x] ++ (flatten r)
--
-- We will prove that, for any tree a,
--    flatten (mirror a) = reverse (flatten a)
-- by induction on a.
--
-- Base case: Suppose that a = Leaf x. Then,
--    flatten (mirror a)
--    = flatten (mirror (Leaf x))
--    = flatten (Leaf x)              [by mirror1]
--    = [x]                           [by flatten1]
--    = reverse [x]
--    = reverse (flatten (Leaf x))    [by flatten1]
--    = reverse (flatten a)
--
-- Induction step: Suppose that a = Node x l r and the induction
-- hypotheses hold:
--    flatten (mirror l) = reverse (flatten l)                        (Hl)
--    flatten (mirror r) = reverse (flatten r)                        (Hr)
-- Then,
--    flatten (mirror a)
--    = flatten (mirror (Node x l r))
--    = flatten (Node x (mirror r) (mirror l))                      [by mirror2]
--    = (flatten (mirror r) ++ [x]) ++ flatten (mirror l)           [by flatten2]
--    = (reverse (flatten r) ++ [x]) ++ flatten (mirror l)          [by Hr]
--    = (reverse (flatten r) ++ [x]) ++ reverse (flatten l)         [by Hl]
--    = (reverse (flatten r) ++ reverse [x]) ++ reverse (flatten l)
--    = reverse ([x] ++ flatten r) ++ reverse (flatten l)
--    = reverse (flatten l ++ ([x] ++ flatten r))
--    = reverse ((flatten l ++ [x]) ++ flatten r)
--    = reverse (flatten (Node x l r))                              [by flatten2]
--    = reverse (flatten a)

-- Proofs with Lean4
-- =================

import Mathlib.Tactic

open List

variable {α : Type}

set_option pp.fieldNotation false

inductive Tree' (α : Type) : Type
  | Leaf : α → Tree' α
  | Node : α → Tree' α → Tree' α → Tree' α

namespace Tree'

variable (a l r : Tree' α)
variable (x : α)

def mirror : Tree' α → Tree' α
  | Leaf x     => Leaf x
  | Node x l r => Node x (mirror r) (mirror l)

@[simp]
lemma mirror_1 :
  mirror (Leaf x) = Leaf x := rfl

@[simp]
lemma mirror_2 :
  mirror (Node x l r) = Node x (mirror r) (mirror l) := rfl

def flatten : Tree' α → List α
  | Leaf x     => [x]
  | Node x l r => (flatten l) ++ [x] ++ (flatten r)

@[simp]
lemma flatten_1 :
  flatten (Leaf x) = [x] := rfl

@[simp]
lemma flatten_2 :
  flatten (Node x l r) = (flatten l) ++ [x] ++ (flatten r) := rfl

-- Proof 1
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ flatten (mirror (Leaf x)) = reverse (flatten (Leaf x))
    rw [mirror_1]
    -- ⊢ flatten (Leaf x) = reverse (flatten (Leaf x))
    rw [flatten_1]
    -- ⊢ [x] = reverse [x]
    rw [reverse_singleton]
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : flatten (mirror l) = reverse (flatten l)
    -- Hr : flatten (mirror r) = reverse (flatten r)
    -- ⊢ flatten (mirror (Node x l r)) = reverse (flatten (Node x l r))
    rw [mirror_2]
    -- ⊢ flatten (Node x (mirror r) (mirror l)) = reverse (flatten (Node x l r))
    rw [flatten_2]
    -- ⊢ flatten (mirror r) ++ [x] ++ flatten (mirror l) = reverse (flatten (Node x l r))
    rw [Hl, Hr]
    -- ⊢ reverse (flatten r) ++ [x] ++ reverse (flatten l) = reverse (flatten (Node x l r))
    rw [flatten_2]
    -- ⊢ reverse (flatten r) ++ [x] ++ reverse (flatten l) = reverse (flatten l ++ [x] ++ flatten r)
    rw [reverse_append]
    -- ⊢ reverse (flatten r) ++ [x] ++ reverse (flatten l) = reverse (flatten r) ++ reverse (flatten l ++ [x])
    rw [reverse_append]
    -- ⊢ reverse (flatten r) ++ [x] ++ reverse (flatten l) = reverse (flatten r) ++ (reverse [x] ++ reverse (flatten l))
    rw [reverse_singleton]
    -- ⊢ reverse (flatten r) ++ [x] ++ reverse (flatten l) = reverse (flatten r) ++ ([x] ++ reverse (flatten l))
    rw [append_assoc]

-- Proof 2
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ flatten (mirror (Leaf x)) = reverse (flatten (Leaf x))
    calc flatten (mirror (Leaf x))
         = flatten (Leaf x)
             := congr_arg flatten (mirror_1 x)
       _ = [x]
             := flatten_1 x
       _ = reverse [x]
             := reverse_singleton x
       _ = reverse (flatten (Leaf x))
             := congr_arg reverse (flatten_1 x).symm
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : flatten (mirror l) = reverse (flatten l)
    -- Hr : flatten (mirror r) = reverse (flatten r)
    -- ⊢ flatten (mirror (Node x l r)) = reverse (flatten (Node x l r))
    calc flatten (mirror (Node x l r))
         = flatten (Node x (mirror r) (mirror l))
             := congr_arg flatten (mirror_2 l r x)
       _ = (flatten (mirror r) ++ [x]) ++ flatten (mirror l)
             := flatten_2 (mirror r) (mirror l) x
       _ = (reverse (flatten r) ++ [x]) ++ flatten (mirror l)
             := congrArg (fun y => (y ++ [x]) ++ flatten (mirror l)) Hr
       _ = (reverse (flatten r) ++ [x]) ++ reverse (flatten l)
             := congrArg ((reverse (flatten r) ++ [x]) ++ .) Hl
       _ = (reverse (flatten r) ++ reverse [x]) ++ reverse (flatten l)
             := congrArg (fun y => (reverse (flatten r) ++ y) ++ reverse (flatten l))
                         (reverse_singleton x).symm
       _ = reverse ([x] ++ flatten r) ++ reverse (flatten l)
             := congrArg (. ++ reverse (flatten l)) (reverse_append [x] (flatten r)).symm
       _ = reverse (flatten l ++ ([x] ++ flatten r))
             := (reverse_append (flatten l) ([x] ++ flatten r)).symm
       _ = reverse ((flatten l ++ [x]) ++ flatten r)
             := congr_arg reverse (append_assoc (flatten l) [x] (flatten r)).symm
       _ = reverse (flatten (Node x l r))
             := congr_arg reverse (flatten_2 l r x)

-- Proof 3
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ flatten (mirror (Leaf x)) = reverse (flatten (Leaf x))
    calc flatten (mirror (Leaf x))
         = flatten (Leaf x)
             := by simp only [mirror_1]
       _ = [x]
             := by rw [flatten_1]
       _ = reverse [x]
             := by rw [reverse_singleton]
       _ = reverse (flatten (Leaf x))
             := by simp only [flatten_1]
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : flatten (mirror l) = reverse (flatten l)
    -- Hr : flatten (mirror r) = reverse (flatten r)
    -- ⊢ flatten (mirror (Node x l r)) = reverse (flatten (Node x l r))
    calc flatten (mirror (Node x l r))
         = flatten (Node x (mirror r) (mirror l))
             := by simp only [mirror_2]
       _ = flatten (mirror r) ++ [x] ++ flatten (mirror l)
             := by rw [flatten_2]
       _ = reverse (flatten r) ++ [x] ++ reverse (flatten l)
             := by rw [Hl, Hr]
       _ = reverse (flatten r) ++ reverse [x] ++ reverse (flatten l)
             := by simp only [reverse_singleton]
       _ = reverse ([x] ++ flatten r) ++ reverse (flatten l)
             := by simp only [reverse_append]
       _ = reverse (flatten l ++ ([x] ++ flatten r))
             := by simp only [reverse_append]
       _ = reverse (flatten l ++ [x] ++ flatten r)
             := by simp only [append_assoc]
       _ = reverse (flatten (Node x l r))
             := by simp only [flatten_2]

-- Proof 4
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ flatten (mirror (Leaf x)) = reverse (flatten (Leaf x))
    calc flatten (mirror (Leaf x))
         = flatten (Leaf x)           := by simp
       _ = [x]                       := by simp
       _ = reverse [x]               := by simp
       _ = reverse (flatten (Leaf x)) := by simp
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : flatten (mirror l) = reverse (flatten l)
    -- Hr : flatten (mirror r) = reverse (flatten r)
    -- ⊢ flatten (mirror (Node x l r)) = reverse (flatten (Node x l r))
    calc flatten (mirror (Node x l r))
         = flatten (Node x (mirror r) (mirror l))
             := by simp
       _ = flatten (mirror r) ++ [x] ++ flatten (mirror l)
             := by simp
       _ = reverse (flatten r) ++ [x] ++ reverse (flatten l)
             := by simp [Hl, Hr]
       _ = reverse (flatten r) ++ reverse [x] ++ reverse (flatten l)
             := by simp
       _ = reverse ([x] ++ flatten r) ++ reverse (flatten l)
             := by simp
       _ = reverse (flatten l ++ ([x] ++ flatten r))
             := by simp
       _ = reverse (flatten l ++ [x] ++ flatten r)
             := by simp
       _ = reverse (flatten (Node x l r))
             := by simp

-- Proof 5
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ flatten (mirror (Leaf x)) = reverse (flatten (Leaf x))
    simp
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : flatten (mirror l) = reverse (flatten l)
    -- Hr : flatten (mirror r) = reverse (flatten r)
    -- ⊢ flatten (mirror (Node x l r)) = reverse (flatten (Node x l r))
    calc flatten (mirror (Node x l r))
        = reverse (flatten r) ++ [x] ++ reverse (flatten l)
            := by simp [Hl, Hr]
      _ = reverse (flatten (Node x l r))
            := by simp

-- Proof 6
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by
  induction a with
  | Leaf _ => simp
  | Node _ _ _ Hl Hr => simp [Hl, Hr]

-- Proof 7
-- =======

example :
  flatten (mirror a) = reverse (flatten a) :=
by induction a <;> simp [*]

-- Proof 8
-- =======

lemma flatten_mirror :
  ∀ a : Tree' α, flatten (mirror a) = reverse (flatten a)
  | Leaf x     => by simp
  | Node x l r => by simp [flatten_mirror l,
                           flatten_mirror r]

end Tree'

-- Used lemmas
-- ===========

-- variable (x : α)
-- variable (xs ys zs : List α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (reverse_append xs ys : reverse (xs ++ ys) = reverse ys ++ reverse xs)
-- #check (reverse_singleton x : reverse [x] = [x])
