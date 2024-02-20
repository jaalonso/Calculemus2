(* Teorema_del_emparedado.lean
-- Teorema del emparedado
-- José A. Alonso Jiménez
-- Sevilla, 19 de febrero de 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que si para todo n, u(n) \<le> v(n) \<le> w(n) y u(n) tiene el
-- mismo límite que, entonces v(n) también tiene dicho límite.
-- ------------------------------------------------------------------ *)

theory Teorema_del_emparedado
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

lemma
  assumes "limite u a"
          "limite w a"
          "\<forall>n. u n \<le> v n"
          "\<forall>n. v n \<le> w n"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume h\<epsilon> : "0 < \<epsilon>"
  obtain N where hN : "\<forall>n\<ge>N. \<bar>u n - a\<bar> < \<epsilon>"
    using assms(1) h\<epsilon> limite_def
    by auto
  obtain N' where hN' : "\<forall>n\<ge>N'. \<bar>w n - a\<bar> < \<epsilon>"
    using assms(2) h\<epsilon> limite_def
    by auto
  have "\<forall>n\<ge>max N N'. \<bar>v n - a\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix n
    assume hn : "n\<ge>max N N'"
    have "v n - a < \<epsilon>"
    proof -
      have "v n - a \<le> w n - a"
        using assms(4) by simp
      also have "\<dots> \<le> \<bar>w n - a\<bar>"
        by simp
      also have "\<dots> < \<epsilon>"
        using hN' hn by auto
      finally show "v n - a < \<epsilon>" .
    qed
    moreover
    have "-(v n - a) < \<epsilon>"
    proof -
      have "-(v n - a) \<le> -(u n - a)"
        using assms(3) by auto
      also have "\<dots> \<le> \<bar>u n - a\<bar>"
        by simp
      also have "\<dots> < \<epsilon>"
        using hN hn by auto
      finally show "-(v n - a) < \<epsilon>" .
    qed
    ultimately show "\<bar>v n - a\<bar> < \<epsilon>"
      by (simp only: abs_less_iff)
  qed
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>v n - a\<bar> < \<epsilon>"
    by (rule exI)
qed

end
