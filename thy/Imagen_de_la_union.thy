(* Imagen_de_la_union.thy
   f[s \<union> t] = f[s] \<union> f[t]
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 13-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   En Isabelle, la imagen de un conjunto s por una función f se representa
   por
      f ` s = {y | \<exists> x, x \<in> s \<and> f x = y}

   Demostrar que
      f ` (s \<union> t) = f ` s \<union> f ` t
  ------------------------------------------------------------------- *)

theory Imagen_de_la_union
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "f ` (s \<union> t) = f ` s \<union> f ` t"
proof (rule equalityI)
  show "f ` (s \<union> t) \<subseteq> f ` s \<union> f ` t"
  proof (rule subsetI)
    fix y
    assume "y \<in> f ` (s \<union> t)"
    then show "y \<in> f ` s \<union> f ` t"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x \<in> s \<union> t"
      then show "y \<in> f ` s \<union> f ` t"
      proof (rule UnE)
        assume "x \<in> s"
        with \<open>y = f x\<close> have "y \<in> f ` s"
          by (simp only: image_eqI)
        then show "y \<in> f ` s \<union> f ` t"
          by (rule UnI1)
      next
        assume "x \<in> t"
        with \<open>y = f x\<close> have "y \<in> f ` t"
          by (simp only: image_eqI)
        then show "y \<in> f ` s \<union> f ` t"
          by (rule UnI2)
      qed
    qed
  qed
next
  show "f ` s \<union> f ` t \<subseteq> f ` (s \<union> t)"
  proof (rule subsetI)
    fix y
    assume "y \<in> f ` s \<union> f ` t"
    then show "y \<in> f ` (s \<union> t)"
    proof (rule UnE)
      assume "y \<in> f ` s"
      then show "y \<in> f ` (s \<union> t)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x \<in> s"
        then have "x \<in> s \<union> t"
          by (rule UnI1)
        with \<open>y = f x\<close> show "y \<in> f ` (s \<union> t)"
          by (simp only: image_eqI)
      qed
    next
      assume "y \<in> f ` t"
      then show "y \<in> f ` (s \<union> t)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x \<in> t"
        then have "x \<in> s \<union> t"
          by (rule UnI2)
        with \<open>y = f x\<close> show "y \<in> f ` (s \<union> t)"
          by (simp only: image_eqI)
      qed
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "f ` (s \<union> t) = f ` s \<union> f ` t"
proof
  show "f ` (s \<union> t) \<subseteq> f ` s \<union> f ` t"
  proof
    fix y
    assume "y \<in> f ` (s \<union> t)"
    then show "y \<in> f ` s \<union> f ` t"
    proof
      fix x
      assume "y = f x"
      assume "x \<in> s \<union> t"
      then show "y \<in> f ` s \<union> f ` t"
      proof
        assume "x \<in> s"
        with \<open>y = f x\<close> have "y \<in> f ` s"
          by simp
        then show "y \<in> f ` s \<union> f ` t"
          by simp
      next
        assume "x \<in> t"
        with \<open>y = f x\<close> have "y \<in> f ` t"
          by simp
        then show "y \<in> f ` s \<union> f ` t"
          by simp
      qed
    qed
  qed
next
  show "f ` s \<union> f ` t \<subseteq> f ` (s \<union> t)"
  proof
    fix y
    assume "y \<in> f ` s \<union> f ` t"
    then show "y \<in> f ` (s \<union> t)"
    proof
      assume "y \<in> f ` s"
      then show "y \<in> f ` (s \<union> t)"
      proof
        fix x
        assume "y = f x"
        assume "x \<in> s"
        then have "x \<in> s \<union> t"
          by simp
        with \<open>y = f x\<close> show "y \<in> f ` (s \<union> t)"
          by simp
      qed
    next
      assume "y \<in> f ` t"
      then show "y \<in> f ` (s \<union> t)"
      proof
        fix x
        assume "y = f x"
        assume "x \<in> t"
        then have "x \<in> s \<union> t"
          by simp
        with \<open>y = f x\<close> show "y \<in> f ` (s \<union> t)"
          by simp
      qed
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "f ` (s \<union> t) = f ` s \<union> f ` t"
  by (simp only: image_Un)

(* 4\<ordfeminine> demostración *)
lemma "f ` (s \<union> t) = f ` s \<union> f ` t"
  by auto

end
