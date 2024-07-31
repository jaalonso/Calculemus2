(* Asociatividad_de_la_concatenacion_de_listas.thy
-- Asociatividad de la concatenación de listas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL la operación de concatenación de listas se representa
-- por (@) y está caracterizada por los siguientes lemas
--    append_Nil  : [] @ ys = ys
--    append_Cons : (x # xs) @ y = x # (xs @ ys)
--
-- Demostrar que la concatenación es asociativa; es decir,
--    xs @ (ys @ zs) = (xs @ ys) @ zs
-- ------------------------------------------------------------------ *)

theory Asociatividad_de_la_concatenacion_de_listas
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  have "[] @ (ys @ zs) = ys @ zs"
    by (simp only: append_Nil)
  also have "\<dots> = ([] @ ys) @ zs"
    by (simp only: append_Nil)
  finally show "[] @ (ys @ zs) = ([] @ ys) @ zs"
    by this
next
  fix x xs
  assume HI : "xs @ (ys @ zs) = (xs @ ys) @ zs"
  have "(x # xs) @ (ys @ zs) = x # (xs @ (ys @ zs))"
    by (simp only: append_Cons)
  also have "\<dots> = x # ((xs @ ys) @ zs)"
    by (simp only: HI)
  also have "\<dots> = (x # (xs @ ys)) @ zs"
    by (simp only: append_Cons)
  also have "\<dots> = ((x # xs) @ ys) @ zs"
    by (simp only: append_Cons)
  finally show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  have "[] @ (ys @ zs) = ys @ zs" by simp
  also have "\<dots> = ([] @ ys) @ zs" by simp
  finally show "[] @ (ys @ zs) = ([] @ ys) @ zs" .
next
  fix x xs
  assume HI : "xs @ (ys @ zs) = (xs @ ys) @ zs"
  have "(x # xs) @ (ys @ zs) = x # (xs @ (ys @ zs))" by simp
  also have "\<dots> = x # ((xs @ ys) @ zs)" by simp
  also have "\<dots> = (x # (xs @ ys)) @ zs" by simp
  also have "\<dots> = ((x # xs) @ ys) @ zs" by simp
  finally show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs" .
qed

(* 3\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  show "[] @ (ys @ zs) = ([] @ ys) @ zs" by simp
next
  fix x xs
  assume "xs @ (ys @ zs) = (xs @ ys) @ zs"
  then show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs" by simp
qed

(* 4\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 5\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by (rule append_assoc [symmetric])

(* 6\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by (induct xs) simp_all

(* 7\<ordfeminine> demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by simp

end
