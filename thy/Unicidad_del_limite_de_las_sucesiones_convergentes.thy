(* Unicidad_del_limite_de_las_sucesiones_convergentes.thy
-- Unicidad del límite de las sucesiones convergentes
-- José A. Alonso Jiménez
-- Sevilla, 12 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar 
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que cada sucesión tiene como máximoun límite.
-- ------------------------------------------------------------------ *)

theory Unicidad_del_limite_de_las_sucesiones_convergentes
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

lemma aux :
  assumes "limite u a"
          "limite u b"
  shows   "b \<le> a"
proof (rule ccontr)
  assume "\<not> b \<le> a"
  let ?\<epsilon> = "b - a"
  have "0 < ?\<epsilon>/2" 
    using \<open>\<not> b \<le> a\<close> by auto
  obtain A where hA : "\<forall>n\<ge>A. \<bar>u n - a\<bar> < ?\<epsilon>/2" 
    using assms(1) limite_def \<open>0 < ?\<epsilon>/2\<close> by blast
  obtain B where hB : "\<forall>n\<ge>B. \<bar>u n - b\<bar> < ?\<epsilon>/2" 
    using assms(2) limite_def \<open>0 < ?\<epsilon>/2\<close> by blast
  let ?C = "max A B"
  have hCa : "\<forall>n\<ge>?C. \<bar>u n - a\<bar> < ?\<epsilon>/2" 
    using hA by simp
  have hCb : "\<forall>n\<ge>?C. \<bar>u n - b\<bar> < ?\<epsilon>/2" 
    using hB by simp
  have "\<forall>n\<ge>?C. \<bar>a - b\<bar> < ?\<epsilon>"
  proof (intro allI impI)
    fix n assume "n \<ge> ?C"
    have "\<bar>a - b\<bar> = \<bar>(a - u n) + (u n - b)\<bar>" by simp
    also have "\<dots> \<le> \<bar>u n - a\<bar> + \<bar>u n - b\<bar>" by simp
    finally show "\<bar>a - b\<bar> < b - a" 
      using hCa hCb \<open>n \<ge> ?C\<close> by fastforce
  qed
  then show False by fastforce
qed

theorem
  assumes "limite u a"
          "limite u b"
  shows   "a = b"
proof (rule antisym)
  show "a \<le> b" using assms(2) assms(1) by (rule aux)
next 
  show "b \<le> a" using assms(1) assms(2) by (rule aux)
qed

end
