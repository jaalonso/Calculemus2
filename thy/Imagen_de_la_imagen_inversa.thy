(* Imagen_de_la_imagen_inversa.thy
   f[f⁻¹[u]] \<subseteq> u.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 19-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Demostrar que
      f ` (f -` u) \<subseteq> u
  ------------------------------------------------------------------- *)

theory Imagen_de_la_imagen_inversa
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f ` (f -` u) \<subseteq> u"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` (f -` u)"
  then show "y \<in> u"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> f -` u"
    then have "f x \<in> u"
      by (rule vimageD)
    with \<open>y = f x\<close> show "y \<in> u"
      by (rule ssubst)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f ` (f -` u) \<subseteq> u"
proof
  fix y
  assume "y \<in> f ` (f -` u)"
  then show "y \<in> u"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> f -` u"
    then have "f x \<in> u"
      by simp
    with \<open>y = f x\<close> show "y \<in> u"
      by simp
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f ` (f -` u) \<subseteq> u"
  by (simp only: image_vimage_subset)

(* 4\<ordfeminine> demostración *)

lemma "f ` (f -` u) \<subseteq> u"
  by auto

end
