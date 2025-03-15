(* El_problema_de_los_infectados.thy
   El problema de los infectados.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 19-marzo-2020
   ================================================================== *)

(* ---------------------------------------------------------------------
   Decidir si es cierto que
      "Existe una persona tal que si dicha persona se infecta, entonces
      todas las personas se infectan."

   El problema consiste en completar la siguiente teoría de Isabelle/HOL:
      theory El_problema_de_los_infectados
      imports Main

      begin

      lemma "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))"
        by sorry

      end
   en la que se ha usado I(x) para representar que la persona x está
   infectada.
   ------------------------------------------------------------------- *)

theory El_problema_de_los_infectados
imports Main

begin

(* 1\<ordfeminine> solución (automática) *)
lemma "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))"
  by auto

(* 2\<ordfeminine> solución (estructurada) *)
lemma "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))"
proof -
  have "\<not> (\<forall>y. I y) \<or> (\<forall>y. I y)" ..
  then show "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))"
  proof
    assume "\<not> (\<forall>y. I y)"
    then have "\<exists>y. \<not>(I y)" by auto
    then obtain a where "\<not> I a" ..
    then have "I a \<longrightarrow> (\<forall>y. I y)" by auto
    then show "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))" ..
  next
    assume "\<forall>y. I y"
    then show "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))" by auto
  qed
qed

(* 3\<ordfeminine> solución (detallada con lemas auxiliares) *)

lemma aux1:
  assumes "\<not> (\<forall>y. I y)"
  shows "\<exists>y. \<not>(I y)"
proof (rule ccontr)
  assume "\<nexists>y. \<not> I y"
  have "\<forall>y. I y"
  proof
    fix a
    show "I a"
    proof (rule ccontr)
      assume "\<not> I a"
      then have "\<exists>y. \<not> I y" by (rule exI)
      with \<open>\<nexists>y. \<not> I y\<close> show False by (rule notE)
    qed
  qed
  with assms show False by (rule notE)
qed

lemma aux2:
  assumes "\<not>P"
  shows   "P \<longrightarrow> Q"
proof
  assume "P"
  with assms show "Q" by (rule notE)
qed

lemma aux3:
  assumes "\<nexists>x. P x"
  shows   "\<forall>x. \<not> P x"
proof
  fix a
  show "\<not> P a"
  proof
    assume "P a"
    then have "\<exists>x. P x" by (rule exI)
    with assms show False by (rule notE)
  qed
qed

lemma aux4:
  assumes "Q"
  shows   "\<exists>x. (P x \<longrightarrow> Q)"
proof (rule ccontr)
  assume "\<nexists>x. (P x \<longrightarrow> Q)"
  then have "\<forall>x. \<not> (P x \<longrightarrow> Q)" by (rule aux3)
  then have "\<not> (P a \<longrightarrow> Q)" by (rule allE)
  moreover
  have "P a \<longrightarrow> Q"
  proof
    assume "P a"
    show "Q" using assms by this
  qed
  ultimately show False by (rule notE)
qed

lemma "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))"
proof -
  have "\<not> (\<forall>y. I y) \<or> (\<forall>y. I y)" by (rule excluded_middle)
  then show "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))"
  proof (rule disjE)
    assume "\<not> (\<forall>y. I y)"
    then have "\<exists>y. \<not>(I y)" by (rule aux1)
    then obtain a where "\<not> I a" by (rule exE)
    then have "I a \<longrightarrow> (\<forall>y. I y)" by (rule aux2)
    then show "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))" by (rule exI)
  next
    assume "\<forall>y. I y"
    then show "\<exists>x. (I x \<longrightarrow> (\<forall>y. I y))" by (rule aux4)
  qed
qed

end
