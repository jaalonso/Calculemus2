(* Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.lean
-- Los supremos de las sucesiones crecientes son sus límites
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea u una sucesión creciente. Demostrar que si M es un supremo de u,
-- entonces el límite de u es M.
-- ------------------------------------------------------------------ *)

theory Los_supremos_de_las_sucesiones_crecientes_son_sus_limites
imports Main HOL.Real
begin

(* (limite u c) expresa que el límite de u es c. *)
definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> \<le> \<epsilon>)"

(* (supremo u M) expresa que el supremo de u es M. *)
definition supremo :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "supremo u M \<longleftrightarrow> ((\<forall>n. u n \<le> M) \<and> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. u n \<ge> M - \<epsilon>))"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "mono u"
          "supremo u M"
  shows   "limite u M"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  have hM : "((\<forall>n. u n \<le> M) \<and> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. u n \<ge> M - \<epsilon>))"
    using assms(2)
    by (simp add: supremo_def)
  then have "\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. u n \<ge> M - \<epsilon>"
    by (rule conjunct2)
  then have "\<exists>k. \<forall>n\<ge>k. u n \<ge> M - \<epsilon>"
    by (simp only: \<open>0 < \<epsilon>\<close>)
  then obtain n0 where "\<forall>n\<ge>n0. u n \<ge> M - \<epsilon>"
    by (rule exE)
  have "\<forall>n\<ge>n0. \<bar>u n - M\<bar> \<le> \<epsilon>"
  proof (intro allI impI)
    fix n
    assume "n \<ge> n0"
    show "\<bar>u n - M\<bar> \<le> \<epsilon>"
    proof (rule abs_leI)
      have "\<forall>n. u n \<le> M"
        using hM by (rule conjunct1)
      then have "u n - M \<le> M - M"
        by simp
      also have "\<dots> = 0"
        by (simp only: diff_self)
      also have "\<dots> \<le> \<epsilon>"
        using \<open>0 < \<epsilon>\<close> by (simp only: less_imp_le)
      finally show "u n - M \<le> \<epsilon>"
        by this
    next
      have "-\<epsilon> = (M - \<epsilon>) - M"
        by simp
      also have "\<dots> \<le> u n - M"
        using \<open>\<forall>n\<ge>n0. M - \<epsilon> \<le> u n\<close> \<open>n0 \<le> n\<close> by auto
      finally have "-\<epsilon> \<le> u n - M"
        by this
      then show "- (u n - M) \<le> \<epsilon>"
        by simp
    qed
  qed
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n - M\<bar> \<le> \<epsilon>"
    by (rule exI)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "mono u"
          "supremo u M"
  shows   "limite u M"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  have hM : "((\<forall>n. u n \<le> M) \<and> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. u n \<ge> M - \<epsilon>))"
    using assms(2)
    by (simp add: supremo_def)
  then have "\<exists>k. \<forall>n\<ge>k. u n \<ge> M - \<epsilon>"
    using \<open>0 < \<epsilon>\<close> by presburger
  then obtain n0 where "\<forall>n\<ge>n0. u n \<ge> M - \<epsilon>"
    by (rule exE)
  then have "\<forall>n\<ge>n0. \<bar>u n - M\<bar> \<le> \<epsilon>"
    using hM by auto
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n - M\<bar> \<le> \<epsilon>"
    by (rule exI)
qed

end
