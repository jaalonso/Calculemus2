(* Equivalencia_de_inversos_iguales_al_neutro.thy
-- Equivalencia de inversos iguales al neutro
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea M un monoide y a, b \<in> M tales que a * b = 1. Demostrar que a = 1
-- si y sólo si b = 1.
-- ------------------------------------------------------------------ *)

theory Equivalencia_de_inversos_iguales_al_neutro
imports Main
begin

context monoid
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows   "a = \<^bold>1 \<longleftrightarrow> b = \<^bold>1"
proof (rule iffI)
  assume "a = \<^bold>1"
  have "b = \<^bold>1 \<^bold>* b"       by (simp only: left_neutral)
  also have "\<dots> = a \<^bold>* b" by (simp only: \<open>a = \<^bold>1\<close>)
  also have "\<dots> = \<^bold>1"     by (simp only: \<open>a \<^bold>* b = \<^bold>1\<close>)
  finally show "b = \<^bold>1"   by this
next
  assume "b = \<^bold>1"
  have "a = a \<^bold>* \<^bold>1"       by (simp only: right_neutral)
  also have "\<dots> = a \<^bold>* b" by (simp only: \<open>b = \<^bold>1\<close>)
  also have "\<dots> = \<^bold>1"     by (simp only: \<open>a \<^bold>* b = \<^bold>1\<close>)
  finally show "a = \<^bold>1"   by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows   "a = \<^bold>1 \<longleftrightarrow> b = \<^bold>1"
proof
  assume "a = \<^bold>1"
  have "b = \<^bold>1 \<^bold>* b"       by simp
  also have "\<dots> = a \<^bold>* b" using \<open>a = \<^bold>1\<close> by simp
  also have "\<dots> = \<^bold>1"     using \<open>a \<^bold>* b = \<^bold>1\<close> by simp
  finally show "b = \<^bold>1"   .
next
  assume "b = \<^bold>1"
  have "a = a \<^bold>* \<^bold>1"       by simp
  also have "\<dots> = a \<^bold>* b" using \<open>b = \<^bold>1\<close> by simp
  also have "\<dots> = \<^bold>1"     using \<open>a \<^bold>* b = \<^bold>1\<close> by simp
  finally show "a = \<^bold>1"   .
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows   "a = \<^bold>1 \<longleftrightarrow> b = \<^bold>1"
  by (metis assms left_neutral right_neutral)

end

end
