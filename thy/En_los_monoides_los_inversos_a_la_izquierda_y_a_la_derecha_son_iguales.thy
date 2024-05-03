(* En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.thy
-- En los monoides, los inversos a la izquierda y a la derecha son iguales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  3-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Un [monoide](https://en.wikipedia.org/wiki/Monoid) es un conjunto
-- junto con una operación binaria que es asociativa y tiene elemento
-- neutro.
--
-- En Lean, está definida la clase de los monoides (como `monoid`) y sus
-- propiedades características son
--    assoc         : (a * b) * c = a * (b * c)
--    left_neutral  : 1 * a = a
--    right_neutral : a * 1 = a
--
-- Demostrar que si M es un monide, a \<in> M, b es un inverso de a por la
-- izquierda y c es un inverso de a por la derecha, entonce b = c.
-- ------------------------------------------------------------------ *)

theory En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales
imports Main
begin

context monoid
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "b \<^bold>* a = \<^bold>1"
          "a \<^bold>* c = \<^bold>1"
  shows   "b = c"
proof -
  have      "b  = b \<^bold>* \<^bold>1"       by (simp only: right_neutral)
  also have "\<dots> = b \<^bold>* (a \<^bold>* c)" by (simp only: \<open>a \<^bold>* c = \<^bold>1\<close>)
  also have "\<dots> = (b \<^bold>* a) \<^bold>* c" by (simp only: assoc)
  also have "\<dots> = \<^bold>1 \<^bold>* c"       by (simp only: \<open>b \<^bold>* a = \<^bold>1\<close>)
  also have "\<dots> = c"           by (simp only: left_neutral)
  finally show "b = c"         by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "b \<^bold>* a = \<^bold>1"
          "a \<^bold>* c = \<^bold>1"
  shows   "b = c"
proof -
  have      "b  = b \<^bold>* \<^bold>1"       by simp
  also have "\<dots> = b \<^bold>* (a \<^bold>* c)" using \<open>a \<^bold>* c = \<^bold>1\<close> by simp
  also have "\<dots> = (b \<^bold>* a) \<^bold>* c" by (simp add: assoc)
  also have "\<dots> = \<^bold>1 \<^bold>* c"       using \<open>b \<^bold>* a = \<^bold>1\<close> by simp
  also have "\<dots> = c"           by simp
  finally show "b = c"         by this
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "b \<^bold>* a = \<^bold>1"
          "a \<^bold>* c = \<^bold>1"
  shows   "b = c"
  using assms
  by (metis assoc left_neutral right_neutral)

end

end
