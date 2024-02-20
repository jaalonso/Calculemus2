(* Producto_de_sucesiones_convergentes_a_cero.lean
-- Producto de sucesiones convergentes a cero
-- José A. Alonso Jiménez
-- Sevilla, 17 de febrero de 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que si las sucesiones u(n) y v(n) convergen a cero,
-- entonces u(n)\<sqdot>v(n) también converge a cero.
-- ------------------------------------------------------------------ *)

theory Producto_de_sucesiones_convergentes_a_cero
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

lemma
  assumes "limite u 0"
          "limite v 0"
  shows   "limite (\<lambda> n. u n * v n) 0"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume  h\<epsilon> : "0 < \<epsilon>"
  then obtain U where hU : "\<forall>n\<ge>U. \<bar>u n - 0\<bar> < \<epsilon>"
    using assms(1) limite_def
    by auto
  obtain V where hV : "\<forall>n\<ge>V. \<bar>v n - 0\<bar> < 1"
    using h\<epsilon> assms(2) limite_def
    by fastforce
  have "\<forall>n\<ge>max U V. \<bar>u n * v n - 0\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix n
    assume hn : "max U V \<le> n"
    then have "U \<le> n"
      by simp
    then have "\<bar>u n - 0\<bar> < \<epsilon>"
      using hU by blast
    have hnV : "V \<le> n"
      using hn by simp
    then have "\<bar>v n - 0\<bar> < 1"
      using hV by blast
    have "\<bar>u n * v n - 0\<bar> = \<bar>(u n - 0) * (v n - 0)\<bar>"
      by simp
    also have "\<dots> = \<bar>u n - 0\<bar> * \<bar>v n - 0\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> < \<epsilon> * 1"
      using \<open>\<bar>u n - 0\<bar> < \<epsilon>\<close> \<open>\<bar>v n - 0\<bar> < 1\<close>
      by (rule abs_mult_less)
    also have "\<dots> = \<epsilon>"
      by simp
    finally show "\<bar>u n * v n - 0\<bar> < \<epsilon>"
      by this
  qed
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n * v n - 0\<bar> < \<epsilon>"
    by (rule exI)
qed

end
