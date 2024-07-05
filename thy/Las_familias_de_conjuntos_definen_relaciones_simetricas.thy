(* Las_familias_de_conjuntos_definen_relaciones_simetricas.thy
-- Las familias de conjuntos definen relaciones simétricas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Cada familia de conjuntos P define una relación de forma que dos
-- elementos están relacionados si algún conjunto de P contiene a ambos
-- elementos. Se puede definir en Isabelle por
--    definition relacion :: "('a set) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
--      "relacion P x y \<longleftrightarrow> (\<exists>A\<in>P. x \<in> A \<and> y \<in> A)"
--
-- Demostrar que si P es una familia de subconjunt\<^bold>os de X, entonces la
-- relación definida por P es simétrica.
-- ------------------------------------------------------------------ *)

theory Las_familias_de_conjuntos_definen_relaciones_simetricas
imports Main
begin

definition relacion :: "('a set) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "relacion P x y \<longleftrightarrow> (\<exists>A\<in>P. x \<in> A \<and> y \<in> A)"

(* 1\<ordfeminine> demostración *)

lemma "symp (relacion P)"
proof (rule sympI)
  fix x y
  assume "relacion P x y"
  then have "\<exists>A\<in>P. x \<in> A \<and> y \<in> A"
    by (unfold relacion_def)
  then have "\<exists>A\<in>P. y \<in> A \<and> x \<in> A"
  proof (rule bexE)
    fix A
    assume hA1 : "A \<in> P" and hA2 : "x \<in> A \<and> y \<in> A"
    have "y \<in> A \<and> x \<in> A"
      using hA2 by (simp only: conj_commute)
    then show "\<exists>A\<in>P. y \<in> A \<and> x \<in> A"
      using hA1 by (rule bexI)
  qed
  then show "relacion P y x"
    by (unfold relacion_def)
qed

(* 2\<ordfeminine> demostración *)

lemma "symp (relacion P)"
proof (rule sympI)
  fix x y
  assume "relacion P x y"
  then obtain A where "A \<in> P \<and> x \<in> A \<and> y \<in> A"
    using relacion_def
    by metis
  then show "relacion P y x"
    using relacion_def
    by metis
qed

(* 3\<ordfeminine> demostración *)

lemma "symp (relacion P)"
  using relacion_def
  by (metis sympI)

end
