(* Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.thy
-- Las clases de equivalencia de elementos relacionados son iguales
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que las clases de equivalencia de elementos relacionados
-- son iguales.
-- ------------------------------------------------------------------ *)

theory Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales
imports Main
begin

definition clase :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "clase R x = {y. R x y}"

(* En la demostración se usará el siguiente lema del que se presentan
   varias demostraciones. *)

(* 1\<ordfeminine> demostración del lema auxiliar *)

lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y \<subseteq> clase R x"
proof (rule subsetI)
  fix z
  assume "z \<in> clase R y"
  then have "R y z"
    by (simp add: clase_def)
  have "transp R"
    using assms(1) by (rule equivp_imp_transp)
  then have "R x z"
    using \<open>R x y\<close> \<open>R y z\<close> by (rule transpD)
  then show "z \<in> clase R x"
    by (simp add: clase_def)
qed

(* 2\<ordfeminine> demostración del lema auxiliar *)

lemma aux :
  assumes "equivp R"
          "R x y"
  shows "clase R y \<subseteq> clase R x"
  using assms
  by (metis clase_def eq_refl equivp_def)

(* A continuación se presentan demostraciones del ejercicio *)

(* 1\<ordfeminine> demostración *)

lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y = clase R x"
proof (rule equalityI)
  show "clase R y \<subseteq> clase R x"
    using assms by (rule aux)
next
  show "clase R x \<subseteq> clase R y"
  proof -
    have "symp R"
      using assms(1) equivpE by blast
    have "R y x"
      using \<open>R x y\<close> by (simp add: \<open>symp R\<close> sympD)
    with assms(1) show "clase R x \<subseteq> clase R y"
       by (rule aux)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y = clase R x"
  using assms
  by (metis clase_def equivp_def)

end
