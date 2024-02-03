(* Limite_de_sucesiones_constantes.thy
-- Límite de sucesiones constantes.
-- José A. Alonso Jiménez
-- Sevilla, 3 de febrero de 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que el límite de la sucesión constante c es c.
-- ------------------------------------------------------------------ *)

theory Limite_de_sucesiones_constantes
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma "limite (\<lambda> n. c) c"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>c - c\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    have "\<forall>n\<ge>0::nat. \<bar>c - c\<bar> < \<epsilon>"
    proof (intro allI impI)
      fix n :: nat
      assume "0 \<le> n"
      have "c - c = 0"
        by (simp only: diff_self)
      then have "\<bar>c - c\<bar> = 0"
        by (simp only: abs_eq_0_iff)
      also have "\<dots> < \<epsilon>"
        by (simp only: \<open>0 < \<epsilon>\<close>)
      finally show "\<bar>c - c\<bar> < \<epsilon>"
        by this
    qed
    then show "\<exists>k::nat. \<forall>n\<ge>k. \<bar>c - c\<bar> < \<epsilon>"
      by (rule exI)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "limite (\<lambda> n. c) c"
proof (unfold limite_def)
  show "\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>c - c\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    have "\<forall>n\<ge>0::nat. \<bar>c - c\<bar> < \<epsilon>"          by (simp add: \<open>0 < \<epsilon>\<close>)
    then show "\<exists>k::nat. \<forall>n\<ge>k. \<bar>c - c\<bar> < \<epsilon>" by (rule exI)
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "limite (\<lambda> n. c) c"
  unfolding limite_def
  by simp

(* 4\<ordfeminine> demostración *)

lemma "limite (\<lambda> n. c) c"
  by (simp add: limite_def)

end
