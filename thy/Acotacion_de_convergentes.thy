(* Acotacion_de_convergentes.lean
-- Las sucesiones convergentes están acotadas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si u es una sucesión convergente, entonces está
-- acotada; es decir,
--     \<exists> k b. \<forall>n\<ge>k. \<bar>u n\<bar> \<le> b
-- ------------------------------------------------------------------- *)

theory Acotacion_de_convergentes
imports Main HOL.Real
begin

(* (limite u c) expresa que el límite de u es c. *)
definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> \<le> \<epsilon>)"

(* (convergente u) expresa que u es convergente. *)
definition convergente :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where
  "convergente u \<longleftrightarrow> (\<exists> a. limite u a)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "convergente u"
  shows   "\<exists> k b. \<forall>n\<ge>k. \<bar>u n\<bar> \<le> b"
proof -
  obtain a where "limite u a"
    using assms convergente_def by blast
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> 1"
    using limite_def zero_less_one by blast
  have "\<forall>n\<ge>k. \<bar>u n\<bar> \<le> 1 + \<bar>a\<bar>"
  proof (intro allI impI)
    fix n
    assume hn : "n \<ge> k"
    have "\<bar>u n\<bar> = \<bar>u n - a + a\<bar>"     by simp
    also have "\<dots> \<le> \<bar>u n - a\<bar> + \<bar>a\<bar>" by simp
    also have "\<dots> \<le> 1 + \<bar>a\<bar>"         by (simp add: hk hn)
    finally show "\<bar>u n\<bar> \<le> 1 + \<bar>a\<bar>"  .
  qed
  then show "\<exists> k b. \<forall>n\<ge>k. \<bar>u n\<bar> \<le> b"
    by (intro exI)
qed

end
