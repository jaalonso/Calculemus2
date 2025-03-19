(* Las_reflexivas_circulares_son_simetricas.thy
   Las reflexivas circulares son simétricas.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 8-abril-2020
   ================================================================== *)

(* ---------------------------------------------------------------------
Se dice que la relación binaria R es
+ reflexiva si \<forall>x. R(x, x)
+ circular si \<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)
+ simétrica si \<forall>x y. R(x, y) \<longrightarrow> R(y, x)

Demostrar que las relaciones reflexivas y circulares son simétricas.
Para ello, hay que completar la siguiente teoría de Isabelle/HOL:
   theory Las_reflexivas_circulares_son_simetricas
   imports Main
   begin

   lemma
     assumes "\<forall>x. R(x, x)"
             "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)"
     shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
     oops

   end
------------------------------------------------------------------- *)

theory Las_reflexivas_circulares_son_simetricas
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)"
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
  using assms
  by blast

(* 2\<ordfeminine> demostración *)
lemma
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)"
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)+
  fix a b
  show "R (a, b) \<longrightarrow> R (b, a)"
  proof (rule impI)
    assume "R(a , b)"
    have "R(b, b)" using assms(1) ..
    with `R(a, b)` have "R(a, b) \<and> R(b, b)" ..
    have  "\<forall>y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)" using assms(2) ..
    then have "\<forall>z. R(a, b) \<and> R(b, z) \<longrightarrow>R(z, a)" ..
    then have "R(a, b) \<and> R(b, b) \<longrightarrow>R(b, a)" ..
    then show "R(b, a)" using `R(a, b) \<and> R(b, b)` ..
  qed
qed

(* 3\<ordmasculine> demostración *)
lemma
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)"
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)+
  fix a b
  show "R (a, b) \<longrightarrow> R (b, a)"
  proof (rule impI)
    assume "R(a, b)"
    have "R(b, b)"
      using assms(1) by (rule allE)
    with `R(a, b)` have "R(a, b) \<and> R(b, b)"
      by (rule conjI)
    have  "\<forall>y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)"
      using assms(2) by (rule allE)
    then have "\<forall>z. R(a, b) \<and> R(b, z) \<longrightarrow>R(z, a)"
      by (rule allE)
    then have "R(a, b) \<and> R(b, b) \<longrightarrow>R(b, a)"
      by (rule allE)
    then show "R(b, a)" using `R(a, b) \<and> R(b, b)`
      by (rule mp)
  qed
qed

end
