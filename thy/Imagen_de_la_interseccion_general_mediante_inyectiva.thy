(* Imagen_de_la_interseccion_general_mediante_inyectiva.thy
-- Imagen de la interseccion general mediante inyectiva
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    \<Inter>ᵢf[Aᵢ] \<subseteq> f[\<Inter>ᵢAᵢ]
-- ------------------------------------------------------------------ *)

theory Imagen_de_la_interseccion_general_mediante_inyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "i \<in> I"
          "inj f"
  shows "(\<Inter> i \<in> I. f ` A i) \<subseteq> f ` (\<Inter> i \<in> I. A i)"
proof (rule subsetI)
  fix y
  assume "y \<in> (\<Inter> i \<in> I. f ` A i)"
  then have "y \<in> f ` A i"
    using \<open>i \<in> I\<close> by (rule INT_D)
  then show "y \<in> f ` (\<Inter> i \<in> I. A i)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> A i"
    have "x \<in> (\<Inter> i \<in> I. A i)"
    proof (rule INT_I)
      fix j
      assume "j \<in> I"
      show "x \<in> A j"
      proof -
        have "y \<in> f ` A j"
          using \<open>y \<in> (\<Inter>i\<in>I. f ` A i)\<close> \<open>j \<in> I\<close> by (rule INT_D)
        then show "x \<in> A j"
        proof (rule imageE)
          fix z
          assume "y = f z"
          assume "z \<in> A j"
          have "f z = f x"
            using \<open>y = f z\<close> \<open>y = f x\<close> by (rule subst)
          with \<open>inj f\<close> have "z = x"
            by (rule injD)
          then show "x \<in> A j"
            using \<open>z \<in> A j\<close> by (rule subst)
        qed
      qed
    qed
    then have "f x \<in> f ` (\<Inter> i \<in> I. A i)"
      by (rule imageI)
    with \<open>y = f x\<close> show "y \<in> f ` (\<Inter> i \<in> I. A i)"
      by (rule ssubst)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "i \<in> I"
          "inj f"
  shows "(\<Inter> i \<in> I. f ` A i) \<subseteq> f ` (\<Inter> i \<in> I. A i)"
proof
  fix y
  assume "y \<in> (\<Inter> i \<in> I. f ` A i)"
  then have "y \<in> f ` A i" using \<open>i \<in> I\<close> by simp
  then show "y \<in> f ` (\<Inter> i \<in> I. A i)"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> A i"
    have "x \<in> (\<Inter> i \<in> I. A i)"
    proof
      fix j
      assume "j \<in> I"
      show "x \<in> A j"
      proof -
        have "y \<in> f ` A j"
          using \<open>y \<in> (\<Inter>i\<in>I. f ` A i)\<close> \<open>j \<in> I\<close> by simp
        then show "x \<in> A j"
        proof
          fix z
          assume "y = f z"
          assume "z \<in> A j"
          have "f z = f x" using \<open>y = f z\<close> \<open>y = f x\<close> by simp
          with \<open>inj f\<close> have "z = x" by (rule injD)
          then show "x \<in> A j" using \<open>z \<in> A j\<close> by simp
        qed
      qed
    qed
    then have "f x \<in> f ` (\<Inter> i \<in> I. A i)" by simp
    with \<open>y = f x\<close> show "y \<in> f ` (\<Inter> i \<in> I. A i)" by simp
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "i \<in> I"
          "inj f"
  shows "(\<Inter> i \<in> I. f ` A i) \<subseteq> f ` (\<Inter> i \<in> I. A i)"
  using assms
  by (simp add: image_INT)

end
