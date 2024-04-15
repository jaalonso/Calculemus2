(* Imagen_de_la_interseccion_de_aplicaciones_inyectivas.thy
-- Si f es inyectiva, entonces f[s] \<inter> f[t] \<subseteq> f[s \<inter> t].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    f ` s \<inter> f ` t \<subseteq> f ` (s \<inter> t)
-- ------------------------------------------------------------------ *)

theory Imagen_de_la_interseccion_de_aplicaciones_inyectivas
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows "f ` s \<inter> f ` t \<subseteq> f ` (s \<inter> t)"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` s \<inter> f ` t"
  then have "y \<in> f ` s"
    by (rule IntD1)
  then show "y \<in> f ` (s \<inter> t)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> s"
    have "x \<in> t"
    proof -
      have "y \<in> f ` t"
        using \<open>y \<in> f ` s \<inter> f ` t\<close> by (rule IntD2)
      then show "x \<in> t"
      proof (rule imageE)
        fix z
        assume "y = f z"
        assume "z \<in> t"
        have "f x = f z"
          using \<open>y = f x\<close> \<open>y = f z\<close> by (rule subst)
        with \<open>inj f\<close> have "x = z"
          by (simp only: inj_eq)
        then show "x \<in> t"
          using \<open>z \<in> t\<close> by (rule ssubst)
      qed
    qed
    with \<open>x \<in> s\<close> have "x \<in> s \<inter> t"
      by (rule IntI)
    with \<open>y = f x\<close> show "y \<in> f ` (s \<inter> t)"
      by (rule image_eqI)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows "f ` s \<inter> f ` t \<subseteq> f ` (s \<inter> t)"
proof
  fix y
  assume "y \<in> f ` s \<inter> f ` t"
  then have "y \<in> f ` s" by simp
  then show "y \<in> f ` (s \<inter> t)"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s"
    have "x \<in> t"
    proof -
      have "y \<in> f ` t" using \<open>y \<in> f ` s \<inter> f ` t\<close> by simp
      then show "x \<in> t"
      proof
        fix z
        assume "y = f z"
        assume "z \<in> t"
        have "f x = f z" using \<open>y = f x\<close> \<open>y = f z\<close> by simp
        with \<open>inj f\<close> have "x = z" by (simp only: inj_eq)
        then show "x \<in> t" using \<open>z \<in> t\<close> by simp
      qed
    qed
    with \<open>x \<in> s\<close> have "x \<in> s \<inter> t" by simp
    with \<open>y = f x\<close> show "y \<in> f ` (s \<inter> t)" by simp
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows "f ` s \<inter> f ` t \<subseteq> f ` (s \<inter> t)"
  using assms
  by (simp only: image_Int)

(* 4\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows "f ` s \<inter> f ` t \<subseteq> f ` (s \<inter> t)"
  using assms
  unfolding inj_def
  by auto

end
