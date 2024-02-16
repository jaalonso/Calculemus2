(* Limite_multiplicado_por_una_constante.thy
-- Límite multiplicado por una constante
-- José A. Alonso Jiménez
-- Sevilla, 15 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que que si el límite de u(i) es a, entonces el de
-- c*u(i) es c*a.
-- ------------------------------------------------------------------ *)

theory Limite_multiplicado_por_una_constante
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

lemma
  assumes "limite u a"
  shows   "limite (\<lambda> n. c * u n) (c * a)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>c * u n - c * a\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    show "\<exists>k. \<forall>n\<ge>k. \<bar>c * u n - c * a\<bar> < \<epsilon>"
    proof (cases "c = 0")
      assume "c = 0"
      then show "\<exists>k. \<forall>n\<ge>k. \<bar>c * u n - c * a\<bar> < \<epsilon>"
        by (simp add: \<open>0 < \<epsilon>\<close>)
    next
      assume "c \<noteq> 0"
      then have "0 < \<bar>c\<bar>"
        by simp
      then have "0 < \<epsilon>/\<bar>c\<bar>"
        by (simp add: \<open>0 < \<epsilon>\<close>)
      then obtain N where hN : "\<forall>n\<ge>N. \<bar>u n - a\<bar> < \<epsilon>/\<bar>c\<bar>"
        using assms limite_def
        by auto
      have "\<forall>n\<ge>N. \<bar>c * u n - c * a\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix n
        assume "n \<ge> N"
        have "\<bar>c * u n - c * a\<bar> = \<bar>c * (u n - a)\<bar>"
          by argo
        also have "\<dots> = \<bar>c\<bar> * \<bar>u n - a\<bar>"
          by (simp only: abs_mult)
        also have "\<dots> < \<bar>c\<bar> * (\<epsilon>/\<bar>c\<bar>)"
          using hN \<open>n \<ge> N\<close> \<open>0 < \<bar>c\<bar>\<close>
          by (simp only: mult_strict_left_mono)
        finally show "\<bar>c * u n - c * a\<bar> < \<epsilon>"
          using \<open>0 < \<bar>c\<bar>\<close>
          by auto
      qed
      then show "\<exists>k. \<forall>n\<ge>k. \<bar>c * u n - c * a\<bar> < \<epsilon>"
        by (rule exI)
    qed
  qed
qed

end
