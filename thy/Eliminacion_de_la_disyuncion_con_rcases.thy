(* Eliminacion_de_la_disyuncion_con_rcases.lean
-- En \<real>, si x \<noteq> 0 entonces x < 0 ó x > 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Ejercicio. Sea x un número real. Demostrar que si
--    x \<noteq> 0
-- entonces
--    x < 0 \<or> x > 0
 -- ------------------------------------------------------------------- *)

(* Demostración en lenguaje natural
   ================================ *)

(*
Usando el siguiente lema
   (\<forall> x y \<in> \<real>)[x < y \<or> x = y \<or> y < x]
se demuestra distinguiendo tres casos.

Caso 1: Supongamos que x < 0. Entonces, se verifica la disyunción ya
que se verifica su primera parte.

Caso 2: Supongamos que x = 0. Entonces, se tiene una contradicción
con la hipótesis.

Caso 3: Supongamos que x > 0. Entonces, se verifica la disyunción ya
que se verifica su segunda parte.
*)

(* Demostraciones con Isabelle/HOL
   =============================== *)

theory Eliminacion_de_la_disyuncion_con_rcases
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma 
  fixes x :: real
  assumes "x \<noteq> 0" 
  shows "x < 0 \<or> x > 0"
proof (cases "x < 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have "x \<ge> 0" by simp
    with `x \<noteq> 0` have "x > 0" by simp
    then show ?thesis by simp
qed

(* 2\<ordfeminine> demostración *)
lemma 
  fixes x :: real
  assumes "x \<noteq> 0" 
  shows "x < 0 \<or> x > 0"
proof (rule classical)
  assume "\<not> (x < 0 \<or> x > 0)"
  then have "\<not> (x < 0) \<and> \<not> (x > 0)" by simp
  then have "x \<ge> 0 \<and> x \<le> 0" by simp
  then have "x = 0" by arith
  with `x \<noteq> 0` show ?thesis by simp
qed

(* 3\<ordfeminine> demostración *)
lemma 
  fixes x :: real
  assumes "x \<noteq> 0" 
  shows "x < 0 \<or> x > 0"
proof (rule classical)
  assume "\<not> (x < 0 \<or> x > 0)"
  then have "x = 0" by simp
  with `x \<noteq> 0` show ?thesis by simp
qed

(* 4\<ordfeminine> demostración *)
lemma 
  fixes x :: real
  assumes "x \<noteq> 0" 
  shows "x < 0 \<or> x > 0"
using assms by auto

end
