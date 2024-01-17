(* Desigualdad_con_rcases.thy
-- Si (\<exists> x, y \<in> \<real>)[z = x² + y² \<or> z = x² + y² + 1], entonces z \<ge> 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si
--    \<exists> x y, z = x^2 + y^2 \<or> z = x^2 + y^2 + 1
-- entonces
--    z \<ge> 0
-- ------------------------------------------------------------------- *)

(*
Demostración en lenguaje natural
================================

Usaremos los siguientes lemas
   (\<forall> x \<in> \<real>)[x² \<ge> 0]                                              (L1)
   (\<forall> x, y \<in> \<real>)[x \<ge> 0 \<rightarrow> y \<ge> 0 \<rightarrow> x + y \<ge> 0]                        (L2)
   1 \<ge> 0                                                          (L3)

Sean a y b tales que
   z = a² + b² \<or> z = a² + b² + 1
Entonces, por L1, se tiene que
   a² \<ge> 0                                                         (1)
   b² \<ge> 0                                                         (2)

En el primer caso, z = a² + b² y se tiene que z \<ge> 0 por el lema L2
aplicado a (1) y (2).

En el segundo caso, z = a² + b² y se tiene que z \<ge> 0 por el lema L2
aplicado a (1), (2) y L3.
*)

(* Demostraciones con Lean4
   ======================== *)

theory Desigualdad_con_rcases
  imports Main "HOL.Real"
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "\<exists>x y :: real. (z = x^2 + y^2 \<or> z = x^2 + y^2 + 1)"
  shows "z \<ge> 0"
proof -
  obtain x y where hxy: "z = x^2 + y^2 \<or> z = x^2 + y^2 + 1" 
    using assms by auto
  { assume "z = x^2 + y^2"
    have "x^2 + y^2 \<ge> 0" by simp
    then have "z \<ge> 0" using `z = x^2 + y^2` by simp }
  { assume "z = x^2 + y^2 + 1"
    have "x^2 + y^2 \<ge> 0" by simp
    then have "z \<ge> 1" using `z = x^2 + y^2 + 1` by simp }
  with hxy show "z \<ge> 0" by auto
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "\<exists>x y :: real. (z = x^2 + y^2 \<or> z = x^2 + y^2 + 1)"
  shows "z \<ge> 0"
proof -
  obtain x y where hxy: "z = x^2 + y^2 \<or> z = x^2 + y^2 + 1" 
    using assms by auto
  with hxy show "z \<ge> 0" by auto
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "\<exists>x y :: real. (z = x^2 + y^2 \<or> z = x^2 + y^2 + 1)"
  shows "z \<ge> 0"
  using assms by fastforce 

end
