(* El_conjunto_de_las_clases_de_equivalencia_es_una_particion.thy
-- El conjunto de las clases de equivalencia es una partición.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si R es una relación de equivalencia en X, entonces las
-- clases de equivalencia de R es una partición de X.
-- ------------------------------------------------------------------ *)

theory El_conjunto_de_las_clases_de_equivalencia_es_una_particion
imports Main
begin

definition clase :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "clase R x = {y. R x y}"

definition particion :: "('a set) set \<Rightarrow> bool" where
  "particion P \<longleftrightarrow> (\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))) \<and> {} \<notin> P"

lemma
  fixes   R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "equivp R"
  shows   "particion (\<Union>x. {clase R x})" (is "particion ?P")
proof (unfold particion_def; intro conjI)
  show "(\<forall>x. \<exists>B\<in>?P. x \<in> B \<and> (\<forall>C\<in>?P. x \<in> C \<longrightarrow> B = C))"
  proof (intro allI)
    fix x
    have "clase R x \<in> ?P"
      by auto
    moreover have "x \<in> clase R x"
      using assms clase_def equivp_def
      by (metis CollectI)
    moreover have "\<forall>C\<in>?P. x \<in> C \<longrightarrow> clase R x = C"
    proof
      fix C
      assume "C \<in> ?P"
      then obtain y where "C = clase R y"
        by auto
      show "x \<in> C \<longrightarrow> clase R x = C"
      proof
        assume "x \<in> C"
        then have "R y x"
          using \<open>C = clase R y\<close> assms clase_def
          by (metis CollectD)
        then show "clase R x = C"
          using assms \<open>C = clase R y\<close> clase_def equivp_def
          by metis
      qed
    qed
    ultimately show "\<exists>B\<in>?P. x \<in> B \<and> (\<forall>C\<in>?P. x \<in> C \<longrightarrow> B = C)"
      by blast
  qed
next
  show "{} \<notin> ?P"
  proof
    assume "{} \<in> ?P"
    then obtain x where "{} = clase R x"
      by auto
    moreover have "x \<in> clase R x"
      using assms clase_def equivp_def
      by (metis CollectI)
    ultimately show False
      by simp
  qed
qed

end
