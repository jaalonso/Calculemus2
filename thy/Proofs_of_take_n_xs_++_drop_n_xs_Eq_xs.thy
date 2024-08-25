(* Proofs_of_take_n_xs_++_drop_n_xs_Eq_xs.thy
-- Proofs of take n xs ++ drop n xs = xs
-- José A. Alonso https://jaalonso.github.io
-- Seville, August 14, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL the function
--    primrec append :: "'a list ⇒ 'a list ⇒ 'a list" (infixr "@" 65) where
--    append_Nil: "[] @ ys = ys" |
--    append_Cons: "(x#xs) @ ys = x # xs @ ys"
-- is defined such that (xs @ ys) is the list obtained by concatenating
--  xs and ys. For example,
--      [3,5] @ [1,9,7] = [3,5,1,9,7]
-- Furthermore, the functions
--    fun take' :: "nat ⇒ 'a list ⇒ 'a list" where
--      "take' n []           = []"
--    | "take' 0 xs           = []"
--    | "take' (Suc n) (x#xs) = x # (take' n xs)"
--
--    fun drop' :: "nat ⇒ 'a list ⇒ 'a list" where
--      "drop' n []           = []"
--    | "drop' 0 xs           = xs"
--    | "drop' (Suc n) (x#xs) = drop' n xs"
-- are defined such that
-- + (take' n xs) is the list formed by the first n elements of xs. For
--   example,
--      take' 2 [3,5,1,9,7] = [3,5]
-- + (drop' n xs) is the list formed by dropping the first n elements
--   of xs. For example,
--      drop' 2 [3,5,1,9,7] = [1,9,7]
--
-- To prove that
--    take' n xs @ drop' n xs = xs
-- ------------------------------------------------------------------ *)

theory "Proofs_of_take_n_xs_++_drop_n_xs_Eq_xs"
imports Main
begin

fun take' :: "nat ⇒ 'a list ⇒ 'a list" where
  "take' n []           = []"
| "take' 0 xs           = []"
| "take' (Suc n) (x#xs) = x # (take' n xs)"

fun drop' :: "nat ⇒ 'a list ⇒ 'a list" where
  "drop' n []           = []"
| "drop' 0 xs           = xs"
| "drop' (Suc n) (x#xs) = drop' n xs"

(* Proof 1 *)

lemma "take' n xs @ drop' n xs = xs"
proof (induct rule: take'.induct)
  fix n
  have "take' n [] @ drop' n [] = [] @ drop' n []"
    by (simp only: take'.simps(1))
  also have "… = drop' n []"
    by (simp only: append.simps(1))
  also have "… = []"
    by (simp only: drop'.simps(1))
  finally show "take' n [] @ drop' n [] = []"
    by this
next
  fix x :: 'a and xs :: "'a list"
  have "take' 0 (x#xs) @ drop' 0 (x#xs) =
        [] @ drop' 0 (x#xs)"
    by (simp only: take'.simps(2))
  also have "… = drop' 0 (x#xs)"
    by  (simp only: append.simps(1))
  also have "… = x # xs"
    by  (simp only: drop'.simps(2))
  finally show "take' 0 (x#xs) @ drop' 0 (x#xs) = x#xs"
    by this
next
  fix n :: nat and x :: 'a and xs :: "'a list"
  assume HI: "take' n xs @ drop' n xs = xs"
  have "take' (Suc n) (x # xs) @ drop' (Suc n) (x # xs) =
        (x # (take' n xs)) @ drop' n xs"
    by (simp only: take'.simps(3)
                   drop'.simps(3))
  also have "… = x # (take' n xs @ drop' n xs)"
    by (simp only: append.simps(2))
  also have "… = x#xs"
    by (simp only: HI)
  finally show "take' (Suc n) (x#xs) @ drop' (Suc n) (x#xs) =
                x#xs"
    by this
qed

(* Proof 2 *)

lemma "take' n xs @ drop' n xs = xs"
proof (induct rule: take'.induct)
case (1 n)
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 n x xs)
  then show ?case by simp
qed

(* Proof 3 *)

lemma "take' n xs @ drop' n xs = xs"
by (induct rule: take'.induct) simp_all

end
