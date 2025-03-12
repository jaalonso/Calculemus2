(* Celebración del Día Mundial de la Lógica *)

theory Celebracion_del_DML
imports Main

begin

(* 1\<ordfeminine> solución (automática) *)
lemma "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))"
  by simp

(* 2\<ordfeminine> solución (estructurada) *)
lemma "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))"
proof -
  have "\<not> (\<forall>y. C y) \<or> (\<forall>y. C y)" ..
  then show "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))"
  proof 
    assume "\<not> (\<forall>y. C y)"
    then have "\<exists>y. \<not>(C y)" by simp
    then obtain a where "\<not> C a" ..
    then have "C a \<longrightarrow> (\<forall>y. C y)" by simp
    then show "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))" ..
  next
    assume "\<forall>y. C y"
    then show "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))" by simp
  qed
qed

(* 3\<ordfeminine> solución (detallada con lemas auxiliares) *)

lemma aux1:
  assumes "\<not> (\<forall>y. C y)"
  shows "\<exists>y. \<not>(C y)"
proof (rule ccontr)
  assume "\<nexists>y. \<not> C y"
  have "\<forall>y. C y"
  proof 
    fix a
    show "C a"
    proof (rule ccontr)
      assume "\<not> C a"
      then have "\<exists>y. \<not> C y" by (rule exI)
      with \<open>\<nexists>y. \<not> C y\<close> show False by (rule notE)
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

lemma "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))"
proof -
  have "\<not> (\<forall>y. C y) \<or> (\<forall>y. C y)" ..
  then show "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))"
  proof 
    assume "\<not> (\<forall>y. C y)"
    then have "\<exists>y. \<not>(C y)" by (rule aux1)
    then obtain a where "\<not> C a" by (rule exE)
    then have "C a \<longrightarrow> (\<forall>y. C y)" by (rule aux2)
    then show "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))" by (rule exI)
  next
    assume "\<forall>y. C y"
    then show "\<exists>x. (C x \<longrightarrow> (\<forall>y. C y))" by (rule aux4)
  qed
qed

end
