(* Las_particiones_definen_relaciones_de_equivalencia.thy
-- Las particiones definen relaciones de equivalencia
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-julio-2024
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
-- definida por P es de equivalencia.
-- ------------------------------------------------------------------ *)

theory Las_particiones_definen_relaciones_de_equivalencia
imports Main
begin

definition relacion :: "('a set) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "relacion P x y \<longleftrightarrow> (\<exists>A\<in>P. x \<in> A \<and> y \<in> A)"

definition particion :: "('a set) set \<Rightarrow> bool" where
  "particion P \<longleftrightarrow> (\<forall>x. (\<exists>B\<in>P. x \<in> B \<and> (\<forall>C\<in>P. x \<in> C \<longrightarrow> B = C))) \<and> {} \<notin> P"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "equivp (relacion P)"
proof (rule equivpI)
  show "reflp (relacion P)"
  proof (rule reflpI)
    fix x
    obtain A where "A \<in> P \<and> x \<in> A"
      using assms particion_def by metis
    then show "relacion P x x"
      using relacion_def by metis
  qed
next
  show "symp (relacion P)"
  proof (rule sympI)
    fix x y
    assume "relacion P x y"
    then obtain A where "A \<in> P \<and> x \<in> A \<and> y \<in> A"
      using relacion_def by metis
    then show "relacion P y x"
      using relacion_def by metis
  qed
next
  show "transp (relacion P)"
  proof (rule transpI)
    fix x y z
    assume "relacion P x y" and "relacion P y z"
    obtain A where "A \<in> P" and hA : "x \<in> A \<and> y \<in> A"
      using \<open>relacion P x y\<close> by (meson relacion_def)
    obtain B where "B \<in> P" and hB : "y \<in> B \<and> z \<in> B"
      using \<open>relacion P y z\<close> by (meson relacion_def)
    have "A = B"
    proof -
      obtain C where "C \<in> P"
                 and hC : "y \<in> C \<and> (\<forall>D\<in>P. y \<in> D \<longrightarrow> C = D)"
        using assms particion_def by metis
      then show "A = B"
        using \<open>A \<in> P\<close> \<open>B \<in> P\<close> hA hB by blast
    qed
    then have "x \<in> A \<and> z \<in> A"  using hA hB by auto
    then show "relacion P x z"
      using \<open>A = B\<close> \<open>A \<in> P\<close> relacion_def by metis
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "particion P"
  shows   "equivp (relacion P)"
proof (rule equivpI)
  show "reflp (relacion P)"
    using assms particion_def relacion_def
    by (metis reflpI)
next
  show "symp (relacion P)"
    using assms relacion_def
    by (metis sympI)
next
  show "transp (relacion P)"
    using assms relacion_def particion_def
    by (smt (verit) transpI)
qed

end
