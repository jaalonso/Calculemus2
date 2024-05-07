(* Unicidad_de_inversos_en_monoides.thy
-- Unicidad de inversos en monoides conmutativos.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que en los monoides conmutativos, si un elemento tiene un
-- inverso por la derecha, dicho inverso es único.
-- ------------------------------------------------------------------ *)

theory Unicidad_de_inversos_en_monoides
imports Main
begin

context comm_monoid
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "x \<^bold>* y = \<^bold>1"
          "x \<^bold>* z = \<^bold>1"
  shows "y = z"
proof -
  have "y = \<^bold>1 \<^bold>* y"             by (simp only: left_neutral)
  also have "\<dots> = (x \<^bold>* z) \<^bold>* y" by (simp only: \<open>x \<^bold>* z = \<^bold>1\<close>)
  also have "\<dots> = (z \<^bold>* x) \<^bold>* y" by (simp only: commute)
  also have "\<dots> = z \<^bold>* (x \<^bold>* y)" by (simp only: assoc)
  also have "\<dots> = z \<^bold>* \<^bold>1"       by (simp only: \<open>x \<^bold>* y = \<^bold>1\<close>)
  also have "\<dots> = z"           by (simp only: right_neutral)
  finally show "y = z"         by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "x \<^bold>* y = \<^bold>1"
          "x \<^bold>* z = \<^bold>1"
  shows "y = z"
proof -
  have "y = \<^bold>1 \<^bold>* y"             by simp
  also have "\<dots> = (x \<^bold>* z) \<^bold>* y" using assms(2) by simp
  also have "\<dots> = (z \<^bold>* x) \<^bold>* y" by simp
  also have "\<dots> = z \<^bold>* (x \<^bold>* y)" by simp
  also have "\<dots> = z \<^bold>* \<^bold>1"       using assms(1) by simp
  also have "\<dots> = z"           by simp
  finally show "y = z"         by this
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "x \<^bold>* y = \<^bold>1"
          "x \<^bold>* z = \<^bold>1"
  shows "y = z"
  using assms
  by auto

end

end
