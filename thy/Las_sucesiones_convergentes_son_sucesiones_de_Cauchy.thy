(* Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.thy
-- Las sucesiones convergentes son sucesiones de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante  una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define
-- + a es un límite de la sucesión u , por
--      def limite (u : \<nat> \<rightarrow> \<real>) (a : \<real>) :=
--        \<forall> \<epsilon> > 0, \<exists> N, \<forall> n \<ge> N, \<bar>u n - a\<bar> \<le> \<epsilon>
-- + la sucesión u es convergente por
--      def convergente (u : \<nat> \<rightarrow> \<real>) :=
--        \<exists> l, limite u l
-- + la sucesión u es de Cauchy por
--      def sucesion_cauchy (u : \<nat> \<rightarrow> \<real>) :=
--        \<forall> \<epsilon> > 0, \<exists> N, \<forall> p q, p \<ge> N \<rightarrow> q \<ge> N \<rightarrow> \<bar>u p - u q\<bar> \<le> \<epsilon>
--
-- Demostrar que las sucesiones convergentes son de Cauchy.
-- ------------------------------------------------------------------ *)

theory Las_sucesiones_convergentes_son_sucesiones_de_Cauchy
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

definition suc_convergente :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "suc_convergente u \<longleftrightarrow> (\<exists> l. limite u l)"

definition suc_cauchy :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "suc_cauchy u \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then have "0 < \<epsilon>/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>/2"
    using \<open>0 < \<epsilon> / 2\<close> limite_def by blast
  have "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix p q
    assume hp : "p \<ge> k" and hq : "q \<ge> k"
    then have hp' : "\<bar>u p - a\<bar> < \<epsilon>/2"
      using hk by blast
    have hq' : "\<bar>u q - a\<bar> < \<epsilon>/2"
      using hk hq by blast
    have "\<bar>u p - u q\<bar> = \<bar>(u p - a) + (a - u q)\<bar>"
      by simp
    also have "\<dots> \<le> \<bar>u p - a\<bar>  + \<bar>a - u q\<bar>"
      by simp
    also have "\<dots> = \<bar>u p - a\<bar>  + \<bar>u q - a\<bar>"
      by simp
    also have "\<dots> < \<epsilon>/2 + \<epsilon>/2"
      using hp' hq' by simp
    also have "\<dots> = \<epsilon>"
      by simp
    finally show "\<bar>u p - u q\<bar> < \<epsilon>"
      by this
  qed
  then show "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>"
    by (rule exI)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then have "0 < \<epsilon>/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>/2"
    using \<open>0 < \<epsilon> / 2\<close> limite_def by blast
  have "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix p q
    assume hp : "p \<ge> k" and hq : "q \<ge> k"
    then have hp' : "\<bar>u p - a\<bar> < \<epsilon>/2"
      using hk by blast
    have hq' : "\<bar>u q - a\<bar> < \<epsilon>/2"
      using hk hq by blast
    show "\<bar>u p - u q\<bar> < \<epsilon>"
      using hp' hq' by argo
  qed
  then show "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>"
    by (rule exI)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then have "0 < \<epsilon>/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>/2"
    using \<open>0 < \<epsilon> / 2\<close> limite_def by blast
  have "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>"
    using hk by (smt (z3) field_sum_of_halves)
  then show "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>"
    by (rule exI)
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then have "0 < \<epsilon>/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>/2"
    using \<open>0 < \<epsilon> / 2\<close> limite_def by blast
  then show "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>" 
    by (smt (z3) field_sum_of_halves) 
qed

end
