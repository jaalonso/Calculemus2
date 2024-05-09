(* Unicidad_del_elemento_neutro_en_los_grupos.thy
-- Unicidad del elemento neutro en los grupos
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que un grupo sólo posee un elemento neutro.
-- ------------------------------------------------------------------ *)

theory Unicidad_del_elemento_neutro_en_los_grupos
imports Main
begin

context group
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* e = x"
  shows   "e = \<^bold>1"
proof -
  have "e = \<^bold>1 \<^bold>* e"     by (simp only: left_neutral)
  also have "\<dots> = \<^bold>1"   using assms by (rule allE)
  finally show "e = \<^bold>1" by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* e = x"
  shows   "e = \<^bold>1"
proof -
  have "e = \<^bold>1 \<^bold>* e"     by simp
  also have "\<dots> = \<^bold>1"   using assms by simp
  finally show "e = \<^bold>1" .
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* e = x"
  shows   "e = \<^bold>1"
  using assms
  by (metis left_neutral)

end

end
