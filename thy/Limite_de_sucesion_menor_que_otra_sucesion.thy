(* Limite_de_sucesion_menor_que_otra_sucesion.thy
-- Si (\<forall>n)[uₙ \<le> vₙ], entonces lim uₙ \<le> lim vₙ
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que si u(n) \<rightarrow> a, v(n) \<rightarrow> c y u(n) \<le> v(n) para todo n,
-- entonces a \<le> c.
-- ------------------------------------------------------------------ *)

theory Limite_de_sucesion_menor_que_otra_sucesion
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "limite v c"
          "\<forall>n. u n \<le> v n"
  shows   "a \<le> c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?\<epsilon> = "(a - c) /2"
  have "0 < ?\<epsilon>"
    using \<open>c < a\<close> by simp
  obtain Nu where HNu : "\<forall>n\<ge>Nu. \<bar>u n - a\<bar> < ?\<epsilon>"
    using assms(1) limite_def \<open>0 < ?\<epsilon>\<close> by blast
  obtain Nv where HNv : "\<forall>n\<ge>Nv. \<bar>v n - c\<bar> < ?\<epsilon>"
    using assms(2) limite_def \<open>0 < ?\<epsilon>\<close> by blast
  let ?N = "max Nu Nv"
  have "?N \<ge> Nu"
    by simp
  then have Ha : "\<bar>u ?N - a\<bar> < ?\<epsilon>"
    using HNu by simp
  have "?N \<ge> Nv"
    by simp
  then have Hc : "\<bar>v ?N - c\<bar> < ?\<epsilon>"
    using HNv by simp
  have "a - c < a - c"
  proof -
    have "a - c = (a - u ?N) + (u ?N - c)"
      by simp
    also have "\<dots> \<le> (a - u ?N) + (v ?N - c)"
      using assms(3) by auto
    also have "\<dots> \<le> \<bar>(a - u ?N) + (v ?N - c)\<bar>"
      by (rule abs_ge_self)
    also have "\<dots> \<le> \<bar>a - u ?N\<bar> + \<bar>v ?N - c\<bar>"
      by (rule abs_triangle_ineq)
    also have "\<dots> = \<bar>u ?N - a\<bar> + \<bar>v ?N - c\<bar>"
      by (simp only: abs_minus_commute)
    also have "\<dots> < ?\<epsilon> + ?\<epsilon>"
      using Ha Hc by (simp only: add_strict_mono)
    also have "\<dots> = a - c"
      by (rule field_sum_of_halves)
    finally show "a - c < a - c"
      by this
  qed
  have "\<not> a - c < a - c"
    by (rule less_irrefl)
  then show False
    using \<open>a - c < a - c\<close> by (rule notE)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "limite v c"
          "\<forall>n. u n \<le> v n"
  shows   "a \<le> c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?\<epsilon> = "(a - c) /2"
  have "0 < ?\<epsilon>"
    using \<open>c < a\<close> by simp
  obtain Nu where HNu : "\<forall>n\<ge>Nu. \<bar>u n - a\<bar> < ?\<epsilon>"
    using assms(1) limite_def \<open>0 < ?\<epsilon>\<close> by blast
  obtain Nv where HNv : "\<forall>n\<ge>Nv. \<bar>v n - c\<bar> < ?\<epsilon>"
    using assms(2) limite_def \<open>0 < ?\<epsilon>\<close> by blast
  let ?N = "max Nu Nv"
  have "?N \<ge> Nu"
    by simp
  then have Ha : "\<bar>u ?N - a\<bar> < ?\<epsilon>"
    using HNu by simp
  then have Ha' : "u ?N - a < ?\<epsilon> \<and> -(u ?N - a) < ?\<epsilon>"
    by argo
  have "?N \<ge> Nv"
    by simp
  then have Hc : "\<bar>v ?N - c\<bar> < ?\<epsilon>"
    using HNv by simp
  then have Hc' : "v ?N - c < ?\<epsilon> \<and> -(v ?N - c) < ?\<epsilon>"
    by argo
  have "a - c < a - c"
    using assms(3) Ha' Hc'
    by (smt (verit, best) field_sum_of_halves)
  have "\<not> a - c < a - c"
    by simp
  then show False
    using \<open>a - c < a - c\<close> by simp
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "limite u a"
          "limite v c"
          "\<forall>n. u n \<le> v n"
  shows   "a \<le> c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?\<epsilon> = "(a - c) /2"
  have "0 < ?\<epsilon>"
    using \<open>c < a\<close> by simp
  obtain Nu where HNu : "\<forall>n\<ge>Nu. \<bar>u n - a\<bar> < ?\<epsilon>"
    using assms(1) limite_def \<open>0 < ?\<epsilon>\<close> by blast
  obtain Nv where HNv : "\<forall>n\<ge>Nv. \<bar>v n - c\<bar> < ?\<epsilon>"
    using assms(2) limite_def \<open>0 < ?\<epsilon>\<close> by blast
  let ?N = "max Nu Nv"
  have "?N \<ge> Nu"
    by simp
  then have Ha : "\<bar>u ?N - a\<bar> < ?\<epsilon>"
    using HNu by simp
  then have Ha' : "u ?N - a < ?\<epsilon> \<and> -(u ?N - a) < ?\<epsilon>"
    by argo
  have "?N \<ge> Nv"
    by simp
  then have Hc : "\<bar>v ?N - c\<bar> < ?\<epsilon>"
    using HNv by simp
  then have Hc' : "v ?N - c < ?\<epsilon> \<and> -(v ?N - c) < ?\<epsilon>"
    by argo
  show False
    using assms(3) Ha' Hc'
    by (smt (verit, best) field_sum_of_halves)
qed

end
