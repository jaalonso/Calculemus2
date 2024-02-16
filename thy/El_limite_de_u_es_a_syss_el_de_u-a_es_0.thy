(* El_limite_de_u_es_a_syss_el_de_u_a_es_0.thy
-- El límite de u es a syss el de u-a es 0.
-- José A. Alonso Jiménez
-- Sevilla, 16 de febrero de 2024
-- ----------------------------------------------------------------- *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
--
-- Demostrar que el límite de u(i) es a si y solo si el de u(i)-a es
-- 0.
-- ------------------------------------------------------------------ *)

theory "El_limite_de_u_es_a_syss_el_de_u-a_es_0"
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

(* 1\<ordfeminine> demostración *)

lemma
  "limite u a \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
proof -
  have "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>)"
    by (rule limite_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>(u n - a) - 0\<bar> < \<epsilon>)"
    by simp
  also have "\<dots> \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
    by (rule limite_def[symmetric])
  finally show "limite u a \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  "limite u a \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
proof -
  have "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - a\<bar> < \<epsilon>)"
    by (simp only: limite_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>(u n - a) - 0\<bar> < \<epsilon>)"
    by simp
  also have "\<dots> \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
    by (simp only: limite_def)
  finally show "limite u a \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
    by this
qed

(* 3\<ordfeminine> demostración *)

lemma
  "limite u a \<longleftrightarrow> limite (\<lambda> i. u i - a) 0"
  using limite_def
  by simp

end
