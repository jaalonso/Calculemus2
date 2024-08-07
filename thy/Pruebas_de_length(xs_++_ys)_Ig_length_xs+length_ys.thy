(* Pruebas_de_length(xs_@_ys)_Ig_length_xs+length_ys.thy
-- Pruebas de length(xs @ ys) = length(xs) + length(ys)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-agosto-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Lean están definidas las funciones
--    length :: 'a list \<Rightarrow> nat
--    (@)    :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list
-- tales que
-- + (length xs) es la longitud de xs. Por ejemplo,
--      length [2,3,5,3] = 4
-- + (xs @ ys) es la lista obtenida concatenando xs e ys. Por ejemplo.
--      [1,2] @ [2,3,5,3] = [1,2,2,3,5,3]
-- Dichas funciones están caracterizadas por los siguientes lemas:
--    list.size(3) : length [] = 0
--    list.size(4) : length (x # xs) = length xs + 1
--    append_Nil   : [] @ ys = ys
--    append_Cons  : (x # xs) @ y = x # (xs @ ys)
--
-- Demostrar que
--    length (xs @ ys) = length xs + length ys
-- ------------------------------------------------------------------ *)

theory "Pruebas_de_length(xs_++_ys)_Ig_length_xs+length_ys"
imports Main
begin

(* 1\<ordfeminine> demostración *)

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

(* 2\<ordfeminine> demostración *)

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

(* 3\<ordfeminine> demostración *)

lemma "length (xs @ ys) = length xs + length ys"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 4\<ordfeminine> demostración *)

lemma "length (xs @ ys) = length xs + length ys"
by (induct xs) simp_all

(* 5\<ordfeminine> demostración *)

lemma "length (xs @ ys) = length xs + length ys"
by (fact length_append)

(* Nota: Auto_solve sugiere la demostración anterior. *)

end
