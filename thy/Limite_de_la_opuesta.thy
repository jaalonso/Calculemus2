(* Limite_de_la_opuesta.lean
-- Si el límite de la sucesión uₙ es a, entonces el límite de -uₙ es -a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-junio-2024
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
-- -u(i) es -a.
-- ------------------------------------------------------------------ *)

theory Limite_de_la_opuesta
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
  shows   "limite (\<lambda> n. -u n) (-a)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>-u n - -a\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then obtain N where hN : "\<forall>n\<ge>N. \<bar>u n - a\<bar> < \<epsilon>"
      using assms limite_def
      by auto
    have "\<forall>n\<ge>N. \<bar>-u n - -a\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix n
        assume "n \<ge> N"
        have "\<bar>-u n - -a\<bar> = \<bar>u n - a\<bar>"
          by argo
        also have "\<dots> < \<epsilon>"
          using hN \<open>n \<ge> N\<close>
          by simp
        finally show "\<bar>-u n - -a\<bar> < \<epsilon>"
          by simp
    qed
    then show "\<exists>k. \<forall>n\<ge>k. \<bar>-u n - -a\<bar> < \<epsilon>"
      by (rule exI)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
  shows   "limite (\<lambda> n. -u n) (-a)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>-u n - -a\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then obtain N where hN : "\<forall>n\<ge>N. \<bar>u n - a\<bar> < \<epsilon>"
      using assms limite_def
      by auto
    have "\<forall>n\<ge>N. \<bar>-u n - -a\<bar> < \<epsilon>"
      using hN by fastforce
    then show "\<exists>k. \<forall>n\<ge>k. \<bar>-u n - -a\<bar> < \<epsilon>"
      by (rule exI)
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
  shows   "limite (\<lambda> n. -u n) (-a)"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>-u n - -a\<bar> < \<epsilon>"
    using assms limite_def by force
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
  shows   "limite (\<lambda> n. -u n) (-a)"
using assms limite_def by force

end
