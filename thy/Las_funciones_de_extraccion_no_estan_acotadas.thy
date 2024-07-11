(* Las_funciones_de_extraccion_no_estan_acotadas.thy
-- Las funciones de extracción no están acotadas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción \<phi> tal que \<phi>(n) = 2*n.
--
-- En Isabelle/HOL, se puede definir que \<phi> es una función de
-- extracción por
--    definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
--      "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"
--
-- Demostrar que las funciones de extracción no está acotadas; es decir,
-- que si \<phi> es una función de extracción, entonces
--     \<forall> N N', \<exists> k \<ge> N', \<phi> k \<ge> N
-- ------------------------------------------------------------------ *)

theory Las_funciones_de_extraccion_no_estan_acotadas
imports Main
begin

definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"

(* En la demostración se usará el siguiente lema *)

lemma aux :
  assumes "extraccion \<phi>"
  shows   "n \<le> \<phi> n"
proof (induct n)
  show "0 \<le> \<phi> 0"
    by simp
next
  fix n
  assume HI : "n \<le> \<phi> n"
  also have "\<phi> n < \<phi> (Suc n)"
    using assms extraccion_def by blast
  finally show "Suc n \<le> \<phi> (Suc n)"
    by simp
qed

(* 1\<ordfeminine> demostración *)

lemma
  assumes "extraccion \<phi>"
  shows   "\<forall> N N'. \<exists> k \<ge> N'. \<phi> k \<ge> N"
proof (intro allI)
  fix N N' :: nat
  let ?k = "max N N'"
  have "max N N' \<le> ?k"
    by (rule le_refl)
  then have hk : "N \<le> ?k \<and> N' \<le> ?k"
    by (simp only: max.bounded_iff)
  then have "?k \<ge> N'"
    by (rule conjunct2)
  moreover
  have "N \<le> \<phi> ?k"
  proof -
    have "N \<le> ?k"
      using hk by (rule conjunct1)
    also have "\<dots> \<le> \<phi> ?k"
      using assms by (rule aux)
    finally show "N \<le> \<phi> ?k"
      by this
  qed
  ultimately have "?k \<ge> N' \<and> \<phi> ?k \<ge> N"
    by (rule conjI)
  then show "\<exists>k \<ge> N'. \<phi> k \<ge> N"
    by (rule exI)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "extraccion \<phi>"
  shows   "\<forall> N N'. \<exists> k \<ge> N'. \<phi> k \<ge> N"
proof (intro allI)
  fix N N' :: nat
  let ?k = "max N N'"
  have "?k \<ge> N'"
    by simp
  moreover
  have "N \<le> \<phi> ?k"
  proof -
    have "N \<le> ?k"
      by simp
    also have "\<dots> \<le> \<phi> ?k"
      using assms by (rule aux)
    finally show "N \<le> \<phi> ?k"
      by this
  qed
  ultimately show "\<exists>k \<ge> N'. \<phi> k \<ge> N"
    by blast
qed

end
