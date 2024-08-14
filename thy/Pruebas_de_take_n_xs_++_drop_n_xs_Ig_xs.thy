(* Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs.lean
-- Pruebas de take' n xs @ drop' n xs = xs
-- José A. Alonso Jiménez
-- Sevilla, 13 de agosto de 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL está definida la función
--    primrec append :: "'a list ⇒ 'a list ⇒ 'a list" (infixr "@" 65) where
--    append_Nil: "[] @ ys = ys" |
--    append_Cons: "(x#xs) @ ys = x # xs @ ys"
-- tal que (xs @ ys) es la lista obtenida concatenando xs e ys. Por
-- ejemplo.
--      [3,5] @ [1,9,7] = [3,5,1,9,7]
-- Además, se definen las funciones
--    fun take' :: "nat ⇒ 'a list ⇒ 'a list" where
--      "take' n []           = []"
--    | "take' 0 xs           = []"
--    | "take' (Suc n) (x#xs) = x # (take' n xs)"
--
--    fun drop' :: "nat ⇒ 'a list ⇒ 'a list" where
--      "drop' n []           = []"
--    | "drop' 0 xs           = xs"
--    | "drop' (Suc n) (x#xs) = drop' n xs"
-- tales que
-- + (take' n xs) es la lista formada por los n primeros elementos de
--   xs. Por ejemplo,
--      take' 2 [3,5,1,9,7] = [3,5]
-- + (drop' n xs) es la lista formada drop'ndo los n primeros elementos
--   de xs. Por ejemplo,
--      drop' 2 [3,5,1,9,7] = [1,9,7]
--
-- Demostrar que
--    take' n xs @ drop' n xs = xs
-- ------------------------------------------------------------------ *)

theory "Pruebas_de_take_n_xs_++_drop_n_xs_Ig_xs"
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

(* 1ª demostración *)

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

(* 2ª demostración *)

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

(* 3ª demostración *)

lemma "take' n xs @ drop' n xs = xs"
by (induct rule: take'.induct) simp_all

end
