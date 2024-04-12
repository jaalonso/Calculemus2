(* Imagen_de_la_interseccion.thy
-- f[s \<inter> t] \<subseteq> f[s] \<inter> f[t].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f ` (s \<inter> t) \<subseteq> f ` s \<inter> f ` t
-- ------------------------------------------------------------------ *)

theory Imagen_de_la_interseccion
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f ` (s \<inter> t) \<subseteq> f ` s \<inter> f ` t"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` (s \<inter> t)"
  then have "y \<in> f ` s"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> s \<inter> t"
    have "x \<in> s"
      using \<open>x \<in> s \<inter> t\<close> by (rule IntD1)
    then have "f x \<in> f ` s"
      by (rule imageI)
    with \<open>y = f x\<close> show "y \<in> f ` s"
      by (rule ssubst)
  qed
  moreover
  note \<open>y \<in> f ` (s \<inter> t)\<close>
  then have "y \<in> f ` t"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> s \<inter> t"
    have "x \<in> t"
      using \<open>x \<in> s \<inter> t\<close> by (rule IntD2)
    then have "f x \<in> f ` t"
      by (rule imageI)
    with \<open>y = f x\<close> show "y \<in> f ` t"
      by (rule ssubst)
  qed
  ultimately show "y \<in> f ` s \<inter> f ` t"
    by (rule IntI)
qed

(* 2\<ordfeminine> demostración *)

lemma "f ` (s \<inter> t) \<subseteq> f ` s \<inter> f ` t"
proof
  fix y
  assume "y \<in> f ` (s \<inter> t)"
  then have "y \<in> f ` s"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s \<inter> t"
    have "x \<in> s"
      using \<open>x \<in> s \<inter> t\<close> by simp
    then have "f x \<in> f ` s"
      by simp
    with \<open>y = f x\<close> show "y \<in> f ` s"
      by simp
  qed
  moreover
  note \<open>y \<in> f ` (s \<inter> t)\<close>
  then have "y \<in> f ` t"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s \<inter> t"
    have "x \<in> t"
      using \<open>x \<in> s \<inter> t\<close> by simp
    then have "f x \<in> f ` t"
      by simp
    with \<open>y = f x\<close> show "y \<in> f ` t"
      by simp
  qed
  ultimately show "y \<in> f ` s \<inter> f ` t"
    by simp
qed

(* 3\<ordfeminine> demostración *)

lemma "f ` (s \<inter> t) \<subseteq> f ` s \<inter> f ` t"
proof
  fix y
  assume "y \<in> f ` (s \<inter> t)"
  then obtain x where hx : "y = f x \<and> x \<in> s \<inter> t" by auto
  then have "y = f x" by simp
  have "x \<in> s" using hx by simp
  have "x \<in> t" using hx by simp
  have "y \<in>  f ` s" using \<open>y = f x\<close> \<open>x \<in> s\<close> by simp
  moreover
  have "y \<in>  f ` t" using \<open>y = f x\<close> \<open>x \<in> t\<close> by simp
  ultimately show "y \<in> f ` s \<inter> f ` t"
    by simp
qed

(* 4\<ordfeminine> demostración *)

lemma "f ` (s \<inter> t) \<subseteq> f ` s \<inter> f ` t"
  by (simp only: image_Int_subset)

(* 5\<ordfeminine> demostración *)

lemma "f ` (s \<inter> t) \<subseteq> f ` s \<inter> f ` t"
  by auto

end
