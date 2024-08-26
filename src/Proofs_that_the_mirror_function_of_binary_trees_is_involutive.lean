-- Proofs_that_the_mirror_function_of_binary_trees_is_involutive.lean
-- Proofs that the mirror function of binary trees is involutive.
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 26, 2024
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
-- whose term is
--    Node 3 (Leaf 4) (Node 2 (Leaf 5) (Leaf 1))
--
-- The definition of the function that calculates the mirror image is
--    def mirror : Tree' α → Tree' α
--      | (Leaf x)     => Leaf x
--      | (Node x l r) => Node x (mirror r) (mirror l)
--
-- Prove that the mirror function is involutive; that is,
--    mirror (mirror a) = a
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- From the definition of the mirror function, we have the following
-- lemmas
--    mirror1 : mirror (Leaf x) = Leaf x
--    mirror2 : mirror (Node x l r) = Node x (mirror r) (mirror l)
--
-- We will prove that, for any tree a,
--    mirror (mirror a) = a
-- by induction on a.
--
-- Base case: Suppose that a = Leaf x. Then,
--    mirror (mirror a)
--    = mirror (mirror (Leaf x))
--    = mirror (Leaf x)             [por mirror1]
--    = Leaf x                      [por mirror1]
--    = a
--
-- Induction step: Suppose that a = Node x l r and the induction
-- hypotheses hold:
--    mirror (mirror l) = l                                         (Hl)
--    mirror (mirror r) = r                                         (Hr)
-- Then,
--    mirror (mirror a)
--    = mirror (mirror (Node x l r))
--    = mirror (Node x (mirror r) (mirror l))             [by mirror2]
--    = Node x (mirror (mirror l)) (mirror (mirror r))    [by mirror2]
--    = Node x l (mirror (mirror r))                      [by Hl]
--    = Node x l r                                        [by Hr]
--    = a

-- Proofs whith Lean4
-- ==================

import Mathlib.Tactic

variable {α : Type}

set_option pp.fieldNotation false

inductive Tree' (α : Type) : Type
  | Leaf : α → Tree' α
  | Node : α → Tree' α → Tree' α → Tree' α

namespace Tree'

variable (a l r : Tree' α)
variable (x : α)

def mirror : Tree' α → Tree' α
  | (Leaf x)     => Leaf x
  | (Node x l r) => Node x (mirror r) (mirror l)

@[simp]
lemma mirror_1 :
  mirror (Leaf x) = Leaf x := rfl

@[simp]
lemma mirror_2 :
  mirror (Node x l r) = Node x (mirror r) (mirror l) := rfl

-- Proof 1
-- =======

example :
  mirror (mirror a) = a :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ mirror (mirror (Leaf x)) = Leaf x
    calc mirror (mirror (Leaf x))
         = mirror (Leaf x) := congr_arg mirror (mirror_1 x)
       _ = Leaf x          := mirror_1 x
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : mirror (mirror l) = l
    -- Hr : mirror (mirror r) = r
    -- ⊢ mirror (mirror (Node x l r)) = Node x l r
    calc mirror (mirror (Node x l r))
         = mirror (Node x (mirror r) (mirror l))
             := congr_arg mirror (mirror_2 l r x)
       _ = Node x (mirror (mirror l)) (mirror (mirror r))
             := mirror_2 (mirror r) (mirror l) x
       _ = Node x l (mirror (mirror r))
             := congrArg (Node x . (mirror (mirror r))) Hl
       _ = Node x l r
             := congrArg (Node x l .) Hr

-- Proof 2
-- =======

example :
  mirror (mirror a) = a :=
by
  induction a with
  | Leaf x =>
    -- ⊢ mirror (mirror (Leaf x)) = Leaf x
    calc mirror (mirror (Leaf x))
         = mirror (Leaf x) := congr_arg mirror (mirror_1 x)
       _ = Leaf x          := by rw [mirror_1]
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : mirror (mirror l) = l
    -- Hr : mirror (mirror r) = r
    -- ⊢ mirror (mirror (Node x l r)) = Node x l r
    calc mirror (mirror (Node x l r))
         = mirror (Node x (mirror r) (mirror l))
             := congr_arg mirror (mirror_2 l r x)
       _ = Node x (mirror (mirror l)) (mirror (mirror r))
             := by rw [mirror_2]
       _ = Node x l (mirror (mirror r))
             := by rw [Hl]
       _ = Node x l r
             := by rw [Hr]

-- Proof 3
-- =======

example :
  mirror (mirror a) = a :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ mirror (mirror (Leaf x)) = Leaf x
    calc mirror (mirror (Leaf x))
         = mirror (Leaf x) := by simp
       _ = Leaf x          := by simp
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : mirror (mirror l) = l
    -- Hr : mirror (mirror r) = r
    -- ⊢ mirror (mirror (Node x l r)) = Node x l r
    calc mirror (mirror (Node x l r))
         = mirror (Node x (mirror r) (mirror l))
             := by simp
       _ = Node x (mirror (mirror l)) (mirror (mirror r))
             := by simp
       _ = Node x l (mirror (mirror r))
             := by simp [Hl]
       _ = Node x l r
             := by simp [Hr]

-- Proof 4
-- =======

example :
  mirror (mirror a) = a :=
by
  induction a with
  | Leaf _ => simp
  | Node _ _ _ Hl Hr => simp [Hl, Hr]

-- Proof 5
-- =======

example :
  mirror (mirror a) = a :=
by induction a <;> simp [*]

-- Proof 6
-- =======

example :
  mirror (mirror a) = a :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ mirror (mirror (Leaf x)) = Leaf x
    rw [mirror_1]
    -- ⊢ mirror (Leaf x) = Leaf x
    rw [mirror_1]
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : mirror (mirror l) = l
    -- Hr : mirror (mirror r) = r
    -- ⊢ mirror (mirror (Node x l r)) = Node x l r
    rw [mirror_2]
    -- ⊢ mirror (Node x (mirror r) (mirror l)) = Node x l r
    rw [mirror_2]
    -- ⊢ Node x (mirror (mirror l)) (mirror (mirror r)) = Node x l r
    rw [Hl]
    -- ⊢ Node x l (mirror (mirror r)) = Node x l r
    rw [Hr]

-- Proof 7
-- =======

example :
  mirror (mirror a) = a :=
by
  induction a with
  | Leaf x =>
    -- x : α
    -- ⊢ mirror (mirror (Leaf x)) = Leaf x
    rw [mirror_1, mirror_1]
  | Node x l r Hl Hr =>
    -- x : α
    -- l r : Tree' α
    -- Hl : mirror (mirror l) = l
    -- Hr : mirror (mirror r) = r
    -- ⊢ mirror (mirror (Node x l r)) = Node x l r
    rw [mirror_2, mirror_2, Hl, Hr]

-- Proof 8
-- =======

lemma mirror_mirror :
  ∀ a : Tree' α, mirror (mirror a) = a
  | (Leaf x)     => by simp
  | (Node x l r) => by simp [mirror_mirror l, mirror_mirror r]

end Tree'
