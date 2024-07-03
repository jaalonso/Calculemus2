(* Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.thy
-- Las clases de equivalencia de elementos no relacionados son disjuntas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que las clases de equivalencia de elementos no relacionados
-- son disjuntas.
-- ------------------------------------------------------------------ *)

theory Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas
imports Main
begin

definition clase :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "clase R x = {y. R x y}"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "equivp R"
          "\<not>(R x y)"
  shows "clase R x \<inter> clase R y = {}"
proof -
  have "\<forall>z. z \<in> clase R x \<longrightarrow> z \<notin> clase R y"
  proof (intro allI impI)
    fix z
    assume "z \<in> clase R x"
    then have "R x z"
      using clase_def by (metis CollectD)
    show "z \<notin> clase R y"
    proof (rule notI)
      assume "z \<in> clase R y"
      then have "R y z"
        using clase_def by (metis CollectD)
      then have "R z y"
        using assms(1) by (simp only: equivp_symp)
      with \<open>R x z\<close> have "R x y"
        using assms(1) by (simp only: equivp_transp)
      with \<open>\<not>R x y\<close> show False
        by (rule notE)
    qed
  qed
  then show "clase R x \<inter> clase R y = {}"
    by (simp only: disjoint_iff)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "equivp R"
          "\<not>(R x y)"
  shows "clase R x \<inter> clase R y = {}"
proof -
  have "\<forall>z. z \<in> clase R x \<longrightarrow> z \<notin> clase R y"
  proof (intro allI impI)
    fix z
    assume "z \<in> clase R x"
    then have "R x z"
      using clase_def by fastforce
    show "z \<notin> clase R y"
    proof (rule notI)
      assume "z \<in> clase R y"
      then have "R y z"
        using clase_def by fastforce
      then have "R z y"
        using assms(1) by (simp only: equivp_symp)
      with \<open>R x z\<close> have "R x y"
        using assms(1) by (simp only: equivp_transp)
      with \<open>\<not>R x y\<close> show False
        by simp
    qed
  qed
  then show "clase R x \<inter> clase R y = {}"
    by (simp only: disjoint_iff)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "equivp R"
          "\<not>(R x y)"
  shows "clase R x \<inter> clase R y = {}"
  using assms
  by (metis clase_def
            CollectD
            equivp_symp
            equivp_transp
            disjoint_iff)

(* 4\<ordfeminine> demostración *)

lemma
  assumes "equivp R"
          "\<not>(R x y)"
  shows "clase R x \<inter> clase R y = {}"
  using assms
  by (metis equivp_def
            clase_def
            CollectD
            disjoint_iff_not_equal)

end
