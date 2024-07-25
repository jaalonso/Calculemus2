(* Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.thy
-- Las sucesiones divergentes positivas no_tienen límites finitos.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-julio-2024
-- ------------------------------------------------------------------*)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"
--
-- La sucesión u diverge positivamente cuando, para cada número real A,
-- se puede encontrar un número natural m tal que, para n > m , se tenga
-- u(n) > A. En Isabelle/HOL se puede definir por
--    definition diverge_positivamente :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
--      where "diverge_positivamente u \<longleftrightarrow> (\<forall>A. \<exists>m. \<forall>n\<ge>m. u n > A)"
--
-- Demostrar que si u diverge positivamente, entonces ningún número real
-- es límite de u.
-- ------------------------------------------------------------------ *)

theory Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"

definition diverge_positivamente :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "diverge_positivamente u \<longleftrightarrow> (\<forall>A. \<exists>m. \<forall>n\<ge>m. u n > A)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "diverge_positivamente u"
  shows   "\<nexists>a. limite u a"
proof (rule notI)
  assume "\<exists>a. limite u a"
  then obtain a where "limite u a" try
    by auto
  then obtain m1 where hm1 : "\<forall>n\<ge>m1. \<bar>u n - a\<bar> < 1"
    using limite_def by fastforce
  obtain m2 where hm2 : "\<forall>n\<ge>m2. u n > a + 1"
    using assms diverge_positivamente_def by blast
  let ?m = "max m1 m2"
  have "u ?m < u ?m" using hm1 hm2
  proof -
    have "?m \<ge> m1"
      by (rule max.cobounded1)
    have "?m \<ge> m2"
      by (rule max.cobounded2)
    have "u ?m - a < 1"
      using hm1 \<open>?m \<ge> m1\<close> by fastforce
    moreover have "u ?m > a + 1"
      using hm2 \<open>?m \<ge> m2\<close> by simp
    ultimately show "u ?m < u ?m"
      by simp
  qed
  then show False
    by auto
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "diverge_positivamente u"
  shows   "\<nexists>a. limite u a"
proof (rule notI)
  assume "\<exists>a. limite u a"
  then obtain a where "limite u a" try
    by auto
  then obtain m1 where hm1 : "\<forall>n\<ge>m1. \<bar>u n - a\<bar> < 1"
    using limite_def by fastforce
  obtain m2 where hm2 : "\<forall>n\<ge>m2. u n > a + 1"
    using assms diverge_positivamente_def by blast
  let ?m = "max m1 m2"
  have "1 < 1"
  proof -
    have "1 < u ?m - a"
      using hm2
      by (metis add.commute less_diff_eq max.cobounded2)
    also have "\<dots> < 1"
      using hm1
      by (metis abs_less_iff max_def order_refl)
    finally show "1 < 1" .
  qed
  then show False
    by auto
qed

end
