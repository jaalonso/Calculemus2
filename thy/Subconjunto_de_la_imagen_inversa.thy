(* Subconjunto_de_la_imagen_inversa.thy
   f[s] \<subseteq> u \<leftrightarrow> s \<subseteq> f⁻¹[u]
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 15-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Demostrar que
      f[s] \<subseteq> u \<leftrightarrow> s \<subseteq> f⁻¹[u]
  ------------------------------------------------------------------- *)

theory Subconjunto_de_la_imagen_inversa
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
proof (rule iffI)
  assume "f ` s \<subseteq> u"
  show "s \<subseteq> f -` u"
  proof (rule subsetI)
    fix x
    assume "x \<in> s"
    then have "f x \<in> f ` s"
      by (simp only: imageI)
    then have "f x \<in> u"
      using \<open>f ` s \<subseteq> u\<close> by (rule set_rev_mp)
    then show "x \<in> f -` u"
      by (simp only: vimageI)
  qed
next
  assume "s \<subseteq> f -` u"
  show "f ` s \<subseteq> u"
  proof (rule subsetI)
    fix y
    assume "y \<in> f ` s"
    then show "y \<in> u"
    proof
      fix x
      assume "y = f x"
      assume "x \<in> s"
      then have "x \<in> f -` u"
        using \<open>s \<subseteq> f -` u\<close> by (rule set_rev_mp)
      then have "f x \<in> u"
        by (rule vimageD)
      with \<open>y = f x\<close> show "y \<in> u"
        by (rule ssubst)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
proof
  assume "f ` s \<subseteq> u"
  show "s \<subseteq> f -` u"
  proof
    fix x
    assume "x \<in> s"
    then have "f x \<in> f ` s"
      by simp
    then have "f x \<in> u"
      using \<open>f ` s \<subseteq> u\<close> by (simp add: set_rev_mp)
    then show "x \<in> f -` u"
      by simp
  qed
next
  assume "s \<subseteq> f -` u"
  show "f ` s \<subseteq> u"
  proof
    fix y
    assume "y \<in> f ` s"
    then show "y \<in> u"
    proof
      fix x
      assume "y = f x"
      assume "x \<in> s"
      then have "x \<in> f -` u"
        using \<open>s \<subseteq> f -` u\<close> by (simp only: set_rev_mp)
      then have "f x \<in> u"
        by simp
      with \<open>y = f x\<close> show "y \<in> u"
        by simp
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
  by (simp only: image_subset_iff_subset_vimage)

(* 4\<ordfeminine> demostración *)
lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
  by auto

end
