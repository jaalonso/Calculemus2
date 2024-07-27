(* Limite_de_sucesiones_no_decrecientes.thy
-- Si u es una sucesión no decreciente y su límite es a, entonces u(n) ≤ a para todo n
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u\<^sub>0, u\<^sub>1, u\<^sub>2, u\<^sub>3, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es u\<^sub>n.
--
-- En Isabelle/HOL, se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"
-- y que la sucesión u es no decreciente por
--    definition no_decreciente :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
--      where "no_decreciente u \<longleftrightarrow> (\<forall> n m. n \<le> m \<longrightarrow> u n \<le> u m)"
--
-- Demostrar que si u es una sucesión no decreciente y su límite es a,
-- entonces u(n) \<le> a para todo n.
-- ------------------------------------------------------------------ *)

theory Limite_de_sucesiones_no_decrecientes
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"

definition no_decreciente :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "no_decreciente u \<longleftrightarrow> (\<forall> n m. n \<le> m \<longrightarrow> u n \<le> u m)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "\<forall> n. u n \<le> a"
proof (rule allI)
  fix n
  show "u n \<le> a"
  proof (rule ccontr)
    assume "\<not> u n \<le> a"
    then have "a < u n"
      by (rule not_le_imp_less)
    then have H : "u n - a > 0"
      by (simp only: diff_gt_0_iff_gt)
    then obtain m where hm : "\<forall>p\<ge>m. \<bar>u p - a\<bar> < u n - a"
      using assms(1) limite_def by blast
    let ?k = "max n m"
    have "n \<le> ?k"
      by (simp only: assms(2) no_decreciente_def)
    then have "u n \<le> u ?k"
      using assms(2) no_decreciente_def by blast
    have "\<bar>u ?k - a\<bar> < u n - a"
      by (simp only: hm)
    also have "\<dots> \<le> u ?k - a"
      using \<open>u n \<le> u ?k\<close> by (rule diff_right_mono)
    finally have "\<bar>u ?k - a\<bar> < u ?k - a"
      by this
    then have "\<not> u ?k - a \<le> \<bar>u ?k - a\<bar>"
      by (simp only: not_le_imp_less)
    moreover have "u ?k - a \<le> \<bar>u ?k - a\<bar>"
      by (rule abs_ge_self)
    ultimately show False
      by (rule notE)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "\<forall> n. u n \<le> a"
proof (rule allI)
  fix n
  show "u n \<le> a"
  proof (rule ccontr)
    assume "\<not> u n \<le> a"
    then have H : "u n - a > 0"
      by simp
    then obtain m where hm : "\<forall>p\<ge>m. \<bar>u p - a\<bar> < u n - a"
      using assms(1) limite_def by blast
    let ?k = "max n m"
    have "\<bar>u ?k - a\<bar> < u n - a"
      using hm by simp
    moreover have "u n \<le> u ?k"
      using assms(2) no_decreciente_def by simp
    ultimately have "\<bar>u ?k - a\<bar> < u ?k - a"
      by simp
    then show False
      by simp
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "\<forall> n. u n \<le> a"
proof
  fix n
  show "u n \<le> a"
  proof (rule ccontr)
    assume "\<not> u n \<le> a"
    then obtain m where hm : "\<forall>p\<ge>m. \<bar>u p - a\<bar> < u n - a"
      using assms(1) limite_def by fastforce
    let ?k = "max n m"
    have "\<bar>u ?k - a\<bar> < u n - a"
      using hm by simp
    moreover have "u n \<le> u ?k"
      using assms(2) no_decreciente_def by simp
    ultimately show False
      by simp
  qed
qed

end
