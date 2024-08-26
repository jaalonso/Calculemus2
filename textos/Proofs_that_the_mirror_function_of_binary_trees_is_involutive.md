---
title: Proofs that the mirror function of binary trees is involutive
date: 2024-08-26 06:00:00 UTC+02:00
category: Binary trees
has_math: true
---

[mathjax]

The tree corresponding to

        3
       / \
      2   4
     / \
    1   5

can be represented by the term

    Node 3 (Node 2 (Leaf 1) (Leaf 5)) (Leaf 4)

using the datatype defined by
<pre lang="lean">
   inductive Tree' (α : Type) : Type
     | Leaf : α → Tree' α
     | Node : α → Tree' α → Tree' α → Tree' α
</pre>

The mirror image of the previous tree is

      3
     / \
    4   2
       / \
      5   1

whose term is

    Node 3 (Leaf 4) (Node 2 (Leaf 5) (Leaf 1))

The definition of the function that calculates the mirror image is
<pre lang="lean">
   def mirror : Tree' α → Tree' α
     | (Leaf x)     => Leaf x
     | (Node x l r) => Node x (mirror r) (mirror l)
</pre>

Prove that the mirror function is involutive; that is,
<pre lang="lean">
   mirror (mirror a) = a
</pre>

To do this, complete the following Lean4 theory:

<pre lang="lean">
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

example :
  mirror (mirror a) = a :=
by sorry

end Tree'
</pre>
<!--more-->

<h2>1. Natural language proof</h2>

From the definition of the mirror function, we have the following lemmas
<pre lang="lean">
   mirror1 : mirror (Leaf x) = Leaf x
   mirror2 : mirror (Node x l r) = Node x (mirror r) (mirror l)
</pre>

We will prove that, for any tree a,

    mirror (mirror a) = a

by induction on a.

Base case: Suppose that a = Leaf x. Then,

    mirror (mirror a)
    = mirror (mirror (Leaf x))
    = mirror (Leaf x)             [por mirror1]
    = Leaf x                      [por mirror1]
    = a

Induction step: Suppose that a = Node x l r and the induction hypotheses hold:

    mirror (mirror l) = l                                         (Hl)
    mirror (mirror r) = r                                         (Hr)

Then,

    mirror (mirror a)
    = mirror (mirror (Node x l r))
    = mirror (Node x (mirror r) (mirror l))             [by mirror2]
    = Node x (mirror (mirror l)) (mirror (mirror r))    [by mirror2]
    = Node x l (mirror (mirror r))                      [by Hl]
    = Node x l r                                        [by Hr]
    = a

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
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
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Proofs_that_the_mirror_function_of_binary_trees_is_involutive.lean).

<h2>3. Proof with Isabelle/HOL</h2>

<pre lang="isar">
theory Proofs_that_the_mirror_function_of_binary_trees_is_involutive
imports Main
begin

datatype 'a tree = Leaf "'a"
                  | Node "'a" "'a tree" "'a tree"

fun mirror :: "'a tree ⇒ 'a tree" where
  "mirror (Leaf x)     = (Leaf x)"
| "mirror (Node x l r) = (Node x (mirror r) (mirror l))"

(* Proof 1 *)
lemma
  fixes a :: "'b tree"
  shows "mirror (mirror a) = a" (is "?P a")
proof (induct a)
  fix x
  show "?P (Leaf x)"
    by (simp only: mirror.simps(1))
next
  fix x
  fix l assume h1: "?P l"
  fix r assume h2: "?P r"
  show "?P (Node x l r)"
  proof -
    have "mirror (mirror (Node x l r)) =
          mirror (Node x (mirror r) (mirror l))"
      by (simp only: mirror.simps(2))
    also have "… = Node x (mirror (mirror l)) (mirror (mirror r))"
      by (simp only: mirror.simps(2))
    also have "… = Node x l r"
      by (simp only: h1 h2)
    finally show ?thesis
      by this
 qed
qed

(* Proof 2 *)
lemma
  fixes a :: "'b tree"
  shows "mirror (mirror a) = a" (is "?P a")
proof (induct a)
  fix x
  show "?P (Leaf x)"  by simp
next
  fix x
  fix l assume h1: "?P l"
  fix r assume h2: "?P r"
  show "?P (Node x l r)"
  proof -
    have "mirror (mirror (Node x l r)) =
          mirror (Node x (mirror r) (mirror l))" by simp
    also have "… = Node x (mirror (mirror l)) (mirror (mirror r))"
      by simp
    also have "… = Node x l r" using h1 h2 by simp
    finally show ?thesis .
 qed
qed

(* Proof 3 *)
lemma
  "mirror (mirror a ) = a"
by (induct a) simp_all

end
</pre>
