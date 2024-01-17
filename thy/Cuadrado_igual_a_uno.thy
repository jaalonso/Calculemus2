(* Cuadrado_igual_a_uno.thy
-- En \<real>, si x² = 1 entonces x = 1 ó x = -1.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si
--    x^2 = 1
-- entonces
--    x = 1 \<or> x = -1
-- ------------------------------------------------------------------- *)

(*
Demostración en lenguaje natural
================================

Usaremos los siguientes lemas
   (\<forall> x \<in> \<real>)[x - x = 0]                                           (L1)
   (\<forall> x, y \<in> \<real>)[xy = 0 \<rightarrow> x = 0 \<or> y = 0]                           (L2)
   (\<forall> x, y \<in> \<real>)[x - y = 0 \<leftrightarrow> x = y]                                (L3)
   (\<forall> x, y \<in> \<real>)[x + y = 0 \<rightarrow> x = -y]                               (L4)

Se tiene que
   (x - 1)(x + 1) = x² - 1
                  = 1 - 1      [por la hipótesis]
                  = 0          [por L1]
y, por el lema L2, se tiene que
   x - 1 = 0 \<or> x + 1 = 0
Acabaremos la demostración por casos.

Primer caso:
  x - 1 = 0 \<Longrightarrow> x = 1             [por L3]
            \<Longrightarrow> x = 1 \<or> x = -1

Segundo caso:
  x + 1 = 0 \<Longrightarrow> x = -1            [por L4]
            \<Longrightarrow> x = 1 \<or> x = -1
*)

(* Demostraciones con Isabelle/HOL
   =============================== *)

theory Cuadrado_igual_a_uno
  imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 \<or> x = -1"
proof -
  have "(x - 1) * (x + 1) = x^2 - 1"
    by algebra
  also have "... = 0"
    using assms by simp
  finally have "(x - 1) * (x + 1) = 0" .
  moreover 
  { assume "(x - 1) = 0"
    then have "x = 1"
      by simp }
  moreover 
  { assume "(x + 1) = 0"
    then have "x = -1"
      by simp }
  ultimately show "x = 1 \<or> x = -1"
    by auto
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 \<or> x = -1"
proof -
  have "(x - 1) * (x + 1) = x^2 - 1"
    by algebra
  also have "... = 0"
    using assms by simp
  finally have "(x - 1) * (x + 1) = 0" .
  then show "x = 1 \<or> x = -1"
    by auto
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 \<or> x = -1"
proof -
  have "(x - 1) * (x + 1) = 0"
  proof -
    have "(x - 1) * (x + 1) = x^2 - 1" by algebra
    also have "\<dots> = 0" by (simp add: assms)
    finally show ?thesis .
  qed
  then show "x = 1 \<or> x = -1"
    by auto
qed

(* 4\<ordfeminine> demostración *)
lemma
  fixes x :: real
  assumes "x^2 = 1"
  shows "x = 1 \<or> x = -1"
using assms power2_eq_1_iff by blast

end
