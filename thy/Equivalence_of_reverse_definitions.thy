(* Equivalence_of_reverse_definitions.thy
-- Equivalence of reverse definitions.
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, August 19, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL, the function
--    rev :: "'a list \<Rightarrow> 'a list"
-- is defined such that (rev xs) is the list obtained by reversing
-- the order of  elements in xs, such that the first element becomes the
-- last, the second element becomes the second to last, and so on,
-- resulting in a new list with the same elements but in the opposite
-- sequence. For example,
--    rev  [3,2,5,1] = [1,5,2,3]
--
-- Its definition is
--    primrec rev :: "'a list \<Rightarrow> 'a list" where
--      "rev [] = []"
--    | "rev (x # xs) = rev xs @ [x]"
--
-- An alternative definition is
--    fun reverse_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
--      "reverse_aux [] ys     = ys"
--    | "reverse_aux (x#xs) ys = reverse_aux xs (x#ys)"
--
--    fun reverse :: "'a list \<Rightarrow> 'a list" where
--      "reverse xs = reverse_aux xs []"
--
-- Prove that the two definitions are equivalent; that is,
--    reverse xs = reverse2 xs
-- ------------------------------------------------------------------ *)

theory Equivalence_of_reverse_definitions
imports Main
begin

(* Alternative definition *)
(* ====================== *)

fun reverse_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverse_aux [] ys     = ys"
| "reverse_aux (x#xs) ys = reverse_aux xs (x#ys)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse xs = reverse_aux xs []"

(* Auxiliar lemma: reverse_aux xs ys = (rev xs) @ ys *)
(* ================================================= *)

(* Proof 1 of the auxiliary lemma *)
lemma
  "reverse_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "reverse_aux [] ys = ys"
    by (simp only: reverse_aux.simps(1))
  also have "\<dots> = [] @ ys"
    by (simp only: append.simps(1))
  also have "\<dots> = rev [] @ ys"
    by (simp only: rev.simps(1))
  finally show "reverse_aux [] ys = rev [] @ ys"
    by this
next
  fix a ::'a and xs :: "'a list"
  assume HI: "\<And>ys. reverse_aux xs ys = rev xs@ys"
  show "\<And>ys. reverse_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "reverse_aux (a#xs) ys = reverse_aux xs (a#ys)"
      by (simp only: reverse_aux.simps(2))
    also have "\<dots> = rev xs@(a#ys)"
      by (simp only: HI)
    also have "\<dots> = rev xs @ ([a] @ ys)"
      by (simp only: append.simps)
    also have "\<dots> = (rev xs @ [a]) @ ys"
      by (simp only: append_assoc)
    also have "\<dots> = rev (a # xs) @ ys"
      by (simp only: rev.simps(2))
    finally show "reverse_aux (a#xs) ys = rev (a#xs)@ys"
      by this
  qed
qed

(* Proof 2 of the auxiliary lemma *)
lemma
  "reverse_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "reverse_aux [] ys = ys" by simp
  also have "\<dots> = [] @ ys" by simp
  also have "\<dots> = rev [] @ ys" by simp
  finally show "reverse_aux [] ys = rev [] @ ys" .
next
  fix a ::'a and xs :: "'a list"
  assume HI: "\<And>ys. reverse_aux xs ys = rev xs@ys"
  show "\<And>ys. reverse_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "reverse_aux (a#xs) ys = reverse_aux xs (a#ys)" by simp
    also have "\<dots> = rev xs@(a#ys)" using HI by simp
    also have "\<dots> = rev xs @ ([a] @ ys)" by simp
    also have "\<dots> = (rev xs @ [a]) @ ys" by simp
    also have "\<dots> = rev (a # xs) @ ys" by simp
    finally show "reverse_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* Proof 3 of the auxiliary lemma *)
lemma
  "reverse_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  show "reverse_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume HI: "\<And>ys. reverse_aux xs ys = rev xs@ys"
  show "\<And>ys. reverse_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "reverse_aux (a#xs) ys = rev xs@(a#ys)" using HI by simp
    also have "\<dots> = rev (a # xs) @ ys" by simp
    finally show "reverse_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* Proof 4 of the auxiliary lemma *)
lemma
  "reverse_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  show "\<And>ys. reverse_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume "\<And>ys. reverse_aux xs ys = rev xs@ys"
  then show "\<And>ys. reverse_aux (a#xs) ys = rev (a#xs)@ys" by simp
qed

(* Proof 5 of the auxiliary lemma *)
lemma
  "reverse_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* Proof 6 of the auxiliary lemma *)
lemma reverse_equiv:
  "reverse_aux xs ys = (rev xs) @ ys"
by (induct xs arbitrary: ys) simp_all

(* Proofs of the main lemma *)
(* ======================== *)

(* Proof 1 *)
lemma "reverse xs = rev xs"
proof -
  have "reverse xs = reverse_aux xs []"
    by (rule reverse.simps)
  also have "\<dots> = (rev xs) @ []"
    by (rule reverse_equiv)
  also have "\<dots> = rev xs"
    by (rule append.right_neutral)
  finally show "reverse xs = rev xs"
    by this
qed

(* Proof 2 *)
lemma "reverse xs = rev xs"
proof -
  have "reverse xs = reverse_aux xs []"  by simp
  also have "\<dots> = (rev xs) @ []" by (rule reverse_equiv)
  also have "\<dots> = rev xs" by simp
  finally show "reverse xs = rev xs" .
qed

(* Proof 3 *)
lemma "reverse xs = rev xs"
by (simp add: reverse_equiv)

end
