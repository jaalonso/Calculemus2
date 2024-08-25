(* Proofs_of_the_equality_length(xs++ys)_Eq_length(xs)+length(ys).thy
-- Proofs of the equality length(xs ++ ys) = length(xs) + length(ys).
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 7, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL, the functions
--    length :: 'a list \<Rightarrow> nat
--    (@)    :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list
-- are defined such that
-- + (length xs) is the length of xs. For example,
--      length [2,3,5,3] = 4
-- + (xs @ ys) is the list obtained by concatenating xs and ys. For
--   example.
--      [1,2] @ [2,3,5,3] = [1,2,2,3,5,3]
--
-- These functions are characterized by the following lemmas:
--    list.size(3) : length [] = 0
--    list.size(4) : length (x # xs) = length xs + 1
--    append_Nil   : [] @ ys = ys
--    append_Cons  : (x # xs) @ y = x # (xs @ ys)
--
-- To prove that
--    length (xs @ ys) = length xs + length ys
-- ------------------------------------------------------------------ *)

theory "Proofs_of_the_equality_length(xs++ys)_Eq_length(xs)+length(ys)"
imports Main
begin

(* Proof 1 *)

lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  have "length ([] @ ys) = length ys"
    by (simp only: append_Nil)
  also have "\<dots> = 0 + length ys"
    by (rule add_0 [symmetric])
  also have "\<dots> = length [] + length ys"
    by (simp only: list.size(3))
  finally show "length ([] @ ys) = length [] + length ys"
    by this
next
  fix x xs
  assume HI : "length (xs @ ys) = length xs + length ys"
  have "length ((x # xs) @ ys) = length (x # (xs @ ys))"
    by (simp only: append_Cons)
  also have "\<dots> = length (xs @ ys) + 1"
    by (simp only: list.size(4))
  also have "\<dots> = (length xs + length ys) + 1"
    by (simp only: HI)
  also have "\<dots> = (length xs + 1) + length ys"
    by (simp only: add.assoc add.commute)
  also have "\<dots> = length (x # xs) + length ys"
    by (simp only: list.size(4))
  then show "length ((x # xs) @ ys) = length (x # xs) + length ys"
    by simp
qed

(* Proof 2 *)

lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  show "length ([] @ ys) = length [] + length ys"
    by simp
next
  fix x xs
  assume "length (xs @ ys) = length xs + length ys"
  then show "length ((x # xs) @ ys) = length (x # xs) + length ys"
    by simp
qed

(* Proof 3 *)

lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* Proof 4 *)

lemma "length (xs @ ys) = length xs + length ys"
by (induct xs) simp_all

(* Proof 5 *)

lemma "length (xs @ ys) = length xs + length ys"
by (fact length_append)

(* Note: Auto_solve suggests the previous proof. *)

end
