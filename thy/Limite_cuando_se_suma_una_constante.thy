(* Limite_cuando_se_suma_una_constante.thy
-- Límite con suma de constante
-- José A. Alonso Jiménez
-- Sevilla, 13 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que si el límite de la sucesión u(i) es a y c \<in> \<real>, 
-- entonces el límite de u(i)+c es a+c.
-- ------------------------------------------------------------------ *)

theory Limite_cuando_se_suma_una_constante
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma 
  assumes "limite u a"
  shows   "limite (\<lambda> i.  u i + c)  (a + c)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>(u n + c) - (a + c)\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then have "\<exists>k. \<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>" 
      using assms limite_def by simp
    then obtain k where "\<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>" 
      by (rule exE)
    then have "\<forall>n\<ge>k. \<bar>(u n + c) - (a + c)\<bar> < \<epsilon>" 
      by simp 
    then show "\<exists>k. \<forall>n\<ge>k. \<bar>(u n + c) - (a + c)\<bar> < \<epsilon>"
      by (rule exI)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma 
  assumes "limite u a"
  shows   "limite (\<lambda> i.  u i + c)  (a + c)"
  using assms limite_def
  by simp

end
