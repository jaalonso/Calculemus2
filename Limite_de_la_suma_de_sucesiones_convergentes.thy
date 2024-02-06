(* Limite_de_la_suma_de_sucesiones_convergentes.thy
-- Límite de la suma de sucesiones convergentes
-- José A. Alonso Jiménez
-- Sevilla, 14 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que el límite de la suma de dos sucesiones convergentes es
-- la suma de los límites de dichas sucesiones.
-- ------------------------------------------------------------------ *)

theory Limite_de_la_suma_de_sucesiones_convergentes
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "limite v b"
  shows   "limite (\<lambda> n. u n + v n) (a + b)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>(u n + v n) - (a + b)\<bar> < \<epsilon>"
  proof (intro allI impI) 
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then have "0 < \<epsilon>/2"
      by simp
    then have "\<exists>k. \<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>/2" 
      using assms(1) limite_def by blast
    then obtain Nu where hNu : "\<forall>n\<ge>Nu. \<bar>u n - a\<bar> < \<epsilon>/2" 
      by (rule exE)
    then have "\<exists>k. \<forall>n\<ge>k. \<bar>v n - b\<bar> < \<epsilon>/2" 
      using \<open>0 < \<epsilon>/2\<close> assms(2) limite_def by blast
    then obtain Nv where hNv : "\<forall>n\<ge>Nv. \<bar>v n - b\<bar> < \<epsilon>/2" 
      by (rule exE)
    have "\<forall>n\<ge>max Nu Nv. \<bar>(u n + v n) - (a + b)\<bar> < \<epsilon>" 
    proof (intro allI impI)
      fix n :: nat
      assume "n \<ge> max Nu Nv"
      have "\<bar>(u n + v n) - (a + b)\<bar> = \<bar>(u n - a) + (v n - b)\<bar>" 
        by simp
      also have "\<dots> \<le> \<bar>u n - a\<bar> + \<bar>v n - b\<bar>"                   
        by simp
      also have "\<dots> < \<epsilon>/2 + \<epsilon>/2" 
        using hNu hNv \<open>max Nu Nv \<le> n\<close> by fastforce
      finally show "\<bar>(u n + v n) - (a + b)\<bar> < \<epsilon>" 
        by simp
    qed
    then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n + v n - (a + b)\<bar> < \<epsilon> " 
      by (rule exI)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "limite v b"
  shows   "limite (\<lambda> n. u n + v n) (a + b)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>(u n + v n) - (a + b)\<bar> < \<epsilon>"
  proof (intro allI impI) 
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then have "0 < \<epsilon>/2" by simp
    obtain Nu where hNu : "\<forall>n\<ge>Nu. \<bar>u n - a\<bar> < \<epsilon>/2" 
      using \<open>0 < \<epsilon>/2\<close> assms(1) limite_def by blast
    obtain Nv where hNv : "\<forall>n\<ge>Nv. \<bar>v n - b\<bar> < \<epsilon>/2" 
      using \<open>0 < \<epsilon>/2\<close> assms(2) limite_def by blast
    have "\<forall>n\<ge>max Nu Nv. \<bar>(u n + v n) - (a + b)\<bar> < \<epsilon>" 
      using hNu hNv
      by (smt (verit, ccfv_threshold) field_sum_of_halves max.boundedE)
    then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n + v n - (a + b)\<bar> < \<epsilon> " 
      by blast
  qed
qed

end
