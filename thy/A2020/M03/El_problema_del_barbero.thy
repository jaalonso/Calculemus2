(* El_problema_del_barbero.thy
   El problema del barbero.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 31-marzo-2020
   ================================================================== *)

(* ---------------------------------------------------------------------
   Decidir si es cierto que
      "Carlos afeita a todos los habitantes de Las Chinas que no se
      afeitan a sí mismo y sólo a ellos. Carlos es un habitante de las
      Chinas. Por consiguiente, Carlos no afeita a nadie."

   Se usará la siguiente simbolización:
      A(x,y) para x afeita a y
      C(x)   para x es un habitante de Las Chinas
      c      para Carlos

   El problema consiste en completar la siguiente teoría de Isabelle/HOL:
      theory El_problema_del_barbero
      imports Main
      begin

      lemma
        assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
                "C(c)"
        shows   "\<not>(\<exists>x. A(c,x))"
        oops
      end
   ------------------------------------------------------------------- *)

theory El_problema_del_barbero
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
  using assms
  by auto

(* 2\<ordfeminine> demostración *)
lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
proof -
  have 1: "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" using assms(1) ..
  have "A(c,c)"
  proof (rule ccontr)
    assume "\<not>A(c,c)"
    with assms(2) have "C(c) \<and> \<not>A(c,c)" ..
    with 1 have "A(c,c)" ..
    with \<open>\<not>A(c,c)\<close> show False ..
  qed
  have "\<not>A(c,c)"
  proof -
    have "C(c) \<and> \<not>A(c,c)" using 1 \<open>A(c,c)\<close> ..
    then show "\<not>A(c,c)" ..
  qed
  then show "\<not>(\<exists>x. A(c,x))" using \<open>A(c,c)\<close> ..
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
proof -
  have 1: "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" using assms(1) by (rule allE)
  have "A(c,c)"
  proof (rule ccontr)
    assume "\<not>A(c,c)"
    with assms(2) have "C(c) \<and> \<not>A(c,c)" by (rule conjI)
    with 1 have "A(c,c)" by (rule iffD2)
    with \<open>\<not>A(c,c)\<close> show False by (rule notE)
  qed
  have "\<not>A(c,c)"
  proof -
    have "C(c) \<and> \<not>A(c,c)" using 1 \<open>A(c,c)\<close> by (rule iffD1)
    then show "\<not>A(c,c)" by (rule conjunct2)
  qed
  then show "\<not>(\<exists>x. A(c,x))" using \<open>A(c,c)\<close> by (rule notE)
qed

end
