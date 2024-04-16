(* Imagen_de_la_diferencia_de_conjuntos.thy
-- f[s] \ f[t] \<subseteq> f[s \ t].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f ` s - f ` t \<subseteq> f ` (s - t)
-- ------------------------------------------------------------------- *)

theory Imagen_de_la_diferencia_de_conjuntos
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f ` s - f ` t \<subseteq> f ` (s - t)"
proof (rule subsetI)
  fix y
  assume hy : "y \<in> f ` s - f ` t"
  then show "y \<in> f ` (s - t)"
  proof (rule DiffE)
    assume "y \<in> f ` s"
    assume "y \<notin> f ` t"
    note \<open>y \<in> f ` s\<close>
    then show "y \<in> f ` (s - t)"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x \<in> s"
      have \<open>x \<notin> t\<close>
      proof (rule notI)
        assume "x \<in> t"
        then have "f x \<in> f ` t"
          by (rule imageI)
        with \<open>y = f x\<close> have "y \<in> f ` t"
          by (rule ssubst)
      with \<open>y \<notin> f ` t\<close> show False
        by (rule notE)
    qed
    with \<open>x \<in> s\<close> have "x \<in> s - t"
      by (rule DiffI)
    then have "f x \<in> f ` (s - t)"
      by (rule imageI)
    with \<open>y = f x\<close> show "y \<in> f ` (s - t)"
      by (rule ssubst)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f ` s - f ` t \<subseteq> f ` (s - t)"
proof
  fix y
  assume hy : "y \<in> f ` s - f ` t"
  then show "y \<in> f ` (s - t)"
  proof
    assume "y \<in> f ` s"
    assume "y \<notin> f ` t"
    note \<open>y \<in> f ` s\<close>
    then show "y \<in> f ` (s - t)"
    proof
      fix x
      assume "y = f x"
      assume "x \<in> s"
      have \<open>x \<notin> t\<close>
      proof
        assume "x \<in> t"
        then have "f x \<in> f ` t" by simp
        with \<open>y = f x\<close> have "y \<in> f ` t" by simp
      with \<open>y \<notin> f ` t\<close> show False by simp
    qed
    with \<open>x \<in> s\<close> have "x \<in> s - t" by simp
    then have "f x \<in> f ` (s - t)" by simp
    with \<open>y = f x\<close> show "y \<in> f ` (s - t)" by simp
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f ` s - f ` t \<subseteq> f ` (s - t)"
  by (simp only: image_diff_subset)

(* 4\<ordfeminine> demostración *)

lemma "f ` s - f ` t \<subseteq> f ` (s - t)"
  by auto

end
