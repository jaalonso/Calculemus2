(* Proofs_that_the_mirror_function_of_binary_trees_is_involutive.thy
-- Proofs that the mirror function of binary trees is involutive.
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 26, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- The tree corresponding to
--        3
--       / \
--      2   4
--     / \
--    1   5
-- can be represented by the term
--    Node 3 (Node 2 (Leaf 1) (Leaf 5)) (Leaf 4)
-- using the datatype defined by
--    datatype 'a tree = Leaf "'a"
--                      | Node "'a" "'a tree" "'a tree"
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
--    fun mirror :: "'a tree ⇒ 'a tree" where
--      "mirror (Leaf x)     = (Leaf x)"
--    | "mirror (Node x l r) = (Node x (mirror r) (mirror l))"
--
-- Prove that the mirror function is involutive; that is,
--    mirror (mirror a) = a
-- ------------------------------------------------------------------ *)

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
