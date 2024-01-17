(* Cuadrado_igual_a_cuadrado.thy
-- En \<real>, x² = y² \<rightarrow> x = y \<or> x = -y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si
--    x^2 = y^2
-- entonces
--    x = y \<or> x = -y
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
   (x - y)(x + y) = x² - y²
                  = y² - y²    [por la hipótesis]
                  = 0          [por L1]
y, por el lema L2, se tiene que
   x - y = 0 \<or> x + y = 0

Acabaremos la demostración por casos.

Primer caso:
  x - y = 0 \<Longrightarrow> x = y             [por L3]
            \<Longrightarrow> x = y \<or> x = -y

Segundo caso:
  x + y = 0 \<Longrightarrow> x = -y            [por L4]
            \<Longrightarrow> x = y \<or> x = -y
*)

(* Demostraciones con Isabelle/HOL
   =============================== *)

theory Cuadrado_igual_a_cuadrado
  imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "x^2 = y^2"
  shows "x = y \<or> x = -y"
proof -
  have "(x - y) * (x + y) = x^2 - y^2"
    by algebra
  also have "... = 0"
    using assms by simp
  finally have "(x - y) * (x + y) = 0" .
  moreover
  { assume "(x - y) = 0"
    then have "x = y"
      by simp }
  moreover
  { assume "(x + y) = 0"
    then have "x = -y"
      by simp }
  ultimately show "x = y \<or> x = -y"
    by auto
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "x^2 = y^2"
  shows "x = y \<or> x = -y"
proof -
  have "(x - y) * (x + y) = x^2 - y^2"
    by algebra
  also have "... = 0"
    using assms by simp
  finally have "(x - y) * (x + y) = 0" .
  then show "x = y \<or> x = -y"
    by auto
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "x^2 = y^2"
  shows "x = y \<or> x = -y"
proof -
  have "(x - y) * (x + y) = 0"
  proof -
    have "(x - y) * (x + y) = x^2 - y^2" by algebra
    also have "\<dots> = 0" by (simp add: assms)
    finally show ?thesis .
  qed
  then show "x = y \<or> x = -y"
    by auto
qed

(* 4\<ordfeminine> demostración *)
lemma
  fixes x y :: real
  assumes "x^2 = y^2"
  shows "x = y \<or> x = -y"
  using assms power2_eq_iff by blast

end
