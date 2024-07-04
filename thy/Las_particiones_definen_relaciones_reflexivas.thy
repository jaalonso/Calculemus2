(* Las_particiones_definen_relaciones_reflexivas.thy
-- Las particiones definen relaciones reflexivas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-julio-2024
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
-- definida por P es reflexiva.
-- ------------------------------------------------------------------ *)

theory Las_particiones_definen_relaciones_reflexivas
imports Main
begin

definition relacion :: "('a set) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "relacion P x y \<longleftrightarrow> (\<exists>A\<in>P. x \<in> A \<and> y \<in> A)"

definition particion :: "('a set) set \<Rightarrow> bool" where
  "particion P \<longleftrightarrow> (\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))) \<and> {} \<notin> P"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
proof (rule reflpI)
  fix x
  have "(\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))) \<and> {} \<notin> P"
    using assms by (unfold particion_def)
  then have "\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))"
    by (rule conjunct1)
  then have "\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C)"
    by (rule allE)
  then obtain B where "B \<in> P \<and> (x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))"
    by (rule someI2_bex)
  then obtain B where "(B \<in> P \<and> x \<in> B) \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C)"
    by (simp only: conj_assoc)
  then have "B \<in> P \<and> x \<in> B"
    by (rule conjunct1)
  then have "x \<in> B"
    by (rule conjunct2)
  then have "x \<in> B \<and> x \<in> B"
    using \<open>x \<in> B\<close> by (rule conjI)
  moreover have "B \<in> P"
    using \<open>B \<in> P \<and> x \<in> B\<close> by (rule conjunct1)
  ultimately have "\<exists>B\<in>P. x \<in> B \<and> x \<in> B"
    by (rule bexI)
  then show "relacion P x x"
    by (unfold relacion_def)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
proof (rule reflpI)
  fix x
  obtain A where "A \<in> P \<and> x \<in> A"
    using assms particion_def
    by metis
  then show "relacion P x x"
    using relacion_def
    by metis
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
  using assms particion_def relacion_def
  by (metis reflp_def)

end
