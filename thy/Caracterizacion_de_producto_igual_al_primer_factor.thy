(* Caracterizacion_de_producto_igual_al_primer_factor.thy
-- Caracterización de producto igual al primer factor
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Un monoide cancelativo por la izquierda es un monoide M que cumple la
-- propiedad cancelativa por la izquierda; es decir, para todo a, b \<in> M
--    a * b = a * c \<leftrightarrow> b = c.
--
-- En Isabelle/HOL la clase de los monoides conmutativos cancelativos
-- por la izquierda es
-- cancel_comm_monoid_add y la propiedad cancelativa por la izquierda es
--    add_left_cancel : a + b = a + c \<leftrightarrow> b = c
--
-- Demostrar que si M es un monoide cancelativo por la izquierda y
-- a, b \<in> M, entonces
--    a + b = a \<leftrightarrow> b = 0
-- ------------------------------------------------------------------ *)

theory Caracterizacion_de_producto_igual_al_primer_factor
imports Main
begin

context cancel_comm_monoid_add
begin

(* 1\<ordfeminine> demostración *)

lemma "a + b = a \<longleftrightarrow> b = 0"
proof (rule iffI)
  assume "a + b = a"
  then have "a + b = a + 0"     by (simp only: add_0_right)
  then show "b = 0"             by (simp only: add_left_cancel)
next
  assume "b = 0"
  have "a + 0 = a"              by (simp only: add_0_right)
  with \<open>b = 0\<close> show "a + b = a" by (rule ssubst)
qed

(* 2\<ordfeminine> demostración *)

lemma "a + b = a \<longleftrightarrow> b = 0"
proof
  assume "a + b = a"
  then have "a + b = a + 0" by simp
  then show "b = 0"         by simp
next
  assume "b = 0"
  have "a + 0 = a"          by simp
  then show "a + b = a"     using \<open>b = 0\<close> by simp
qed

(* 3\<ordfeminine> demostración *)

lemma "a + b = a \<longleftrightarrow> b = 0"
proof -
  have "(a + b = a) \<longleftrightarrow> (a + b = a + 0)" by (simp only: add_0_right)
  also have "\<dots> \<longleftrightarrow> (b = 0)"             by (simp only: add_left_cancel)
  finally show "a + b = a \<longleftrightarrow> b = 0"     by this
qed

(* 4\<ordfeminine> demostración *)

lemma "a + b = a \<longleftrightarrow> b = 0"
proof -
  have "(a + b = a) \<longleftrightarrow> (a + b = a + 0)" by simp
  also have "\<dots> \<longleftrightarrow> (b = 0)"             by simp
  finally show "a + b = a \<longleftrightarrow> b = 0"     .
qed

(* 5\<ordfeminine> demostración *)

lemma "a + b = a \<longleftrightarrow> b = 0"
  by (simp only: add_cancel_left_right)

(* 6\<ordfeminine> demostración *)

lemma "a + b = a \<longleftrightarrow> b = 0"
  by auto

end

end
