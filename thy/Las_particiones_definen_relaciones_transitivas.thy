(* Las_particiones_definen_relaciones_transitivas.thy
-- Las particiones definen relaciones transitivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Cada familia de conjuntos P define una relación de forma que dos
-- elementos están relacionados si algún conjunto de P contiene a ambos
-- elementos. Se puede definir en Isabelle por
--    definition relacion :: "('a set) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
--      "relacion P x y \<longleftrightarrow> (\<exists>A\<in>P. x \<in> A \<and> y \<in> A)"
--
-- Una familia de subconjuntos de X es una partición de X si cada elemento
-- de X pertenece a un único conjunto de P y todos los elementos de P
-- son no vacíos. Se puede definir en Isabelle por
--    definition particion :: "('a set) set \<Rightarrow> bool" where
--     "particion P \<longleftrightarrow> (\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))) \<and> {} \<notin> P"
--
-- Demostrar que si P es una partición de X, entonces la relación
-- definida por P es transitiva.
-- ------------------------------------------------------------------ *)

theory Las_particiones_definen_relaciones_transitivas
imports Main
begin

definition relacion :: "('a set) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "relacion P x y \<longleftrightarrow> (\<exists>A\<in>P. x \<in> A \<and> y \<in> A)"

definition particion :: "('a set) set \<Rightarrow> bool" where
  "particion P \<longleftrightarrow> (\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))) \<and> {} \<notin> P"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "transp (relacion P)"
proof (rule transpI)
  fix x y z
  assume "relacion P x y" and "relacion P y z"
  have "\<exists>A\<in>P. x \<in> A \<and> y \<in> A"
    using \<open>relacion P x y\<close>
    by (simp only: relacion_def)
  then obtain A where "A \<in> P" and hA : "x \<in> A \<and> y \<in> A"
    by (rule bexE)
  have "\<exists>B\<in>P. y \<in> B \<and> z \<in> B"
    using \<open>relacion P y z\<close>
    by (simp only: relacion_def)
  then obtain B where "B \<in> P" and hB : "y \<in> B \<and> z \<in> B"
    by (rule bexE)
  have "A = B"
  proof -
    have "\<exists>C \<in> P. y \<in> C \<and> (\<forall>D\<in>P. y \<in> D \<longrightarrow> C = D)"
      using assms
      by (simp only: particion_def)
    then obtain C where "C \<in> P"
                    and hC : "y \<in> C \<and> (\<forall>D\<in>P. y \<in> D \<longrightarrow> C = D)"
      by (rule bexE)
    have hC' : "\<forall>D\<in>P. y \<in> D \<longrightarrow> C = D"
      using hC by (rule conjunct2)
    have "C = A"
      using \<open>A \<in> P\<close> hA hC' by simp
    moreover have "C = B"
      using \<open>B \<in> P\<close> hB hC by simp
    ultimately show "A = B"
      by (rule subst)
  qed
  then have "x \<in> A \<and> z \<in> A"
    using hA hB by simp
  then have "\<exists>A\<in>P. x \<in> A \<and> z \<in> A"
    using \<open>A \<in> P\<close> by (rule bexI)
  then show "relacion P x z"
    using \<open>A = B\<close> \<open>A \<in> P\<close>
    by (unfold relacion_def)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "transp (relacion P)"
proof (rule transpI)
  fix x y z
  assume "relacion P x y" and "relacion P y z"
  obtain A where "A \<in> P" and hA : "x \<in> A \<and> y \<in> A"
    using \<open>relacion P x y\<close>
    by (meson relacion_def)
  obtain B where "B \<in> P" and hB : "y \<in> B \<and> z \<in> B"
    using \<open>relacion P y z\<close>
    by (meson relacion_def)
  have "A = B"
  proof -
    obtain C where "C \<in> P" and hC : "y \<in> C \<and> (\<forall>D\<in>P. y \<in> D \<longrightarrow> C = D)"
      using assms particion_def
      by metis
    have "C = A"
      using \<open>A \<in> P\<close> hA hC by auto
    moreover have "C = B"
      using \<open>B \<in> P\<close> hB hC by auto
    ultimately show "A = B"
      by simp
  qed
  then have "x \<in> A \<and> z \<in> A"
    using hA hB by auto
  then show "relacion P x z"
    using \<open>A = B\<close> \<open>A \<in> P\<close> relacion_def
    by metis
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "transp (relacion P)"
  using assms particion_def relacion_def
  by (smt (verit) transpI)

end
