(* Flatten_of_mirror.lean
-- Proofs of "flatten (mirror a) = reverse (flatten a)"
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 28, 2024
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
-- and the list obtained by flattening it (traversing it in infix order)
-- is
--    [4, 3, 5, 2, 1]
--
-- The definition of the function that calculates the mirror image is
--    fun mirror :: "'a tree \<Rightarrow> 'a tree" where
--      "mirror (Leaf x)     = (Leaf x)"
--    | "mirror (Node x i d) = (Node x (mirror d) (mirror i))"
-- and the one that flattens the tree is
--    fun flatten :: "'a tree \<Rightarrow> 'a list" where
--      "flatten (Leaf x)     = [x]"
--    | "flatten (Node x i d) = (flatten i) @ [x] @ (flatten d)"
--
-- Prove that
--    flatten (mirror a) = rev (flatten a)
-- ------------------------------------------------------------------ *)

theory Flatten_of_mirror
imports Main
begin

datatype 'a tree = Leaf "'a"
                  | Node "'a" "'a tree" "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Leaf x)     = (Leaf x)"
| "mirror (Node x i d) = (Node x (mirror d) (mirror i))"

fun flatten :: "'a tree \<Rightarrow> 'a list" where
  "flatten (Leaf x)     = [x]"
| "flatten (Node x i d) = (flatten i) @ [x] @ (flatten d)"

(* Auxiliary lemma *)
(* =============== *)

(* Proof 1 of the auxiliary lemma *)
lemma "rev [x] = [x]"
proof -
  have "rev [x] = rev [] @ [x]"
    by (simp only: rev.simps(2))
  also have "\<dots> = [] @ [x]"
    by (simp only: rev.simps(1))
  also have "\<dots> = [x]"
    by (simp only: append.simps(1))
  finally show ?thesis
    by this
qed

(* Proof 2 of the auxiliary lemma *)
lemma rev_unit: "rev [x] = [x]"
by simp

(* Main lemma *)
(* ========== *)

(* Proof 1 *)
lemma
  fixes a :: "'b tree"
  shows "flatten (mirror a) = rev (flatten a)" (is "?P a")
proof (induct a)
  fix x :: 'b
  have "flatten (mirror (Leaf x)) = flatten (Leaf x)"
    by (simp only: mirror.simps(1))
  also have "\<dots> = [x]"
    by (simp only: flatten.simps(1))
  also have "\<dots> = rev [x]"
    by (rule rev_unit [symmetric])
  also have "\<dots> = rev (flatten (Leaf x))"
    by (simp only: flatten.simps(1))
  finally show "?P (Leaf x)"
    by this
next
  fix x :: 'b
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (Node x i d)"
  proof -
    have "flatten (mirror (Node x i d)) =
          flatten (Node x (mirror d) (mirror i))"
      by (simp only: mirror.simps(2))
    also have "\<dots> = (flatten (mirror d)) @ [x] @ (flatten (mirror i))"
      by (simp only: flatten.simps(2))
    also have "\<dots> = (rev (flatten d)) @ [x] @ (rev (flatten i))"
      by (simp only: h1 h2)
    also have "\<dots> = rev ((flatten i) @ [x] @ (flatten d))"
      by (simp only: rev_append rev_unit append_assoc)
    also have "\<dots> = rev (flatten (Node x i d))"
      by (simp only: flatten.simps(2))
    finally show ?thesis
      by this
 qed
qed

(* Proof 2 *)
lemma
  fixes a :: "'b tree"
  shows "flatten (mirror a) = rev (flatten a)" (is "?P a")
proof (induct a)
  fix x
  show "?P (Leaf x)" by simp
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (Node x i d)"
  proof -
    have "flatten (mirror (Node x i d)) =
          flatten (Node x (mirror d) (mirror i))" by simp
    also have "\<dots> = (flatten (mirror d)) @ [x] @ (flatten (mirror i))"
      by simp
    also have "\<dots> = (rev (flatten d)) @ [x] @ (rev (flatten i))"
      using h1 h2 by simp
    also have "\<dots> = rev ((flatten i) @ [x] @ (flatten d))" by simp
    also have "\<dots> = rev (flatten (Node x i d))" by simp
    finally show ?thesis .
 qed
qed

(* Proof 3 *)
lemma "flatten (mirror a) = rev (flatten a)"
proof (induct a)
case (Leaf x)
then show ?case by simp
next
  case (Node x i d)
  then show ?case by simp
qed

(* Proof 4 *)
lemma "flatten (mirror a) = rev (flatten a)"
  by (induct a) simp_all

end
