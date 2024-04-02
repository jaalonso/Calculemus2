(* Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.thy
   Si f es suprayectiva, entonces u ⊆ f[f⁻¹[u]].
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla,  2-abril-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Demostrar que si f es suprayectiva, entonces
      u \<subseteq> f ` (f -` u)
  ------------------------------------------------------------------- *)

theory Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
proof (rule subsetI)
  fix y
  assume "y \<in> u"
  have "\<exists>x. y = f x"
    using \<open>surj f\<close> by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x \<in> u"
    using \<open>y \<in> u\<close> by (rule subst)
  then have "x \<in> f -` u"
    by (simp only: vimage_eq)
  then have "f x \<in> f ` (f -` u)"
    by (rule imageI)
  with \<open>y = f x\<close> show "y \<in> f ` (f -` u)"
    by (rule ssubst)
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
proof
  fix y
  assume "y \<in> u"
  have "\<exists>x. y = f x"
    using \<open>surj f\<close> by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x \<in> u"
    using \<open>y \<in> u\<close> by simp
  then have "x \<in> f -` u"
    by simp
  then have "f x \<in> f ` (f -` u)"
    by simp
  with \<open>y = f x\<close> show "y \<in> f ` (f -` u)"
    by simp
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
  using assms
  by (simp only: surj_image_vimage_eq)

(* 4\<ordfeminine> demostración *)
lemma
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
  using assms
  unfolding surj_def
  by auto

(* 5\<ordfeminine> demostración *)
lemma
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
  using assms
  by auto

end
