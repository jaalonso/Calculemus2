(* Desigualdad_triangular_para_valor_absoluto.thy
-- En \<real>, |x + y| \<le> |x| + |y|.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    |x + y| \<le> |x| + |y|
-- ------------------------------------------------------------------- *)

(*
Demostración en lenguaje natural
================================

Se usarán los siguientes lemas
    (\<forall> x \<in> \<real>)[0 \<le> x \<rightarrow> |x| = x]                          (L1)
    (\<forall> a, b, c, d \<in> \<real>)[a \<le> b \<and> c \<le> d \<rightarrow> a + c \<le> b + d]   (L2)
    (\<forall> x \<in> \<real>)[x \<le> |x|]                                  (L3)
    (\<forall> x \<in> \<real>)[x < 0 \<rightarrow> |x| = -x]                         (L4)
    (\<forall> x, y \<in> \<real>)[-(x + y) = -x + -y]                    (L5)
    (\<forall> x \<in> \<real>)[-x \<le> |x|]                                 (L6)

Se demostrará por casos según x + y \<ge> 0:

Primer caso: Supongamos que x + y \<ge> 0. Entonces,
   |x + y| = x + y        [por L1]
         _ \<le> |x| + |y|    [por L2 y L3]

Segundo caso: Supongamos que x + y < 0. Entonces,
   |x + y| = -(x + y)     [por L4]
           = -x + -y      [por L5]
           \<le> |x| + |y|    [por L2 y L6]

*)


(* Demostraciones con Isabelle/HOL
-- =============================== *)

theory Desigualdad_triangular_para_valor_absoluto
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma 
    fixes x y :: real
    shows "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>" 
proof -
  { assume h1: "0 \<le> x + y"
    then have "\<bar>x + y\<bar> = x + y"
      by simp
    also have "... \<le> \<bar>x\<bar> + \<bar>y\<bar>"
      by simp
    finally have "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>" . }
  moreover
  { assume h2: "0 > x + y"
    then have "\<bar>x + y\<bar> = -(x + y)" 
      by simp
    also have "... = -x + -y" 
      by simp
    also have "... \<le> \<bar>x\<bar> + \<bar>y\<bar>" 
      by simp
    finally have "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>" . }
  ultimately show ?thesis 
    by simp
qed

(* 2\<ordfeminine> demostración *)
lemma 
    fixes x y :: real
    shows "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>" 
by (rule abs_triangle_ineq)

(* 3\<ordfeminine> demostración *)
lemma 
    fixes x y :: real
    shows "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>" 
by simp

end
