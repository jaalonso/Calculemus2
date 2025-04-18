(* Monotonia_de_la_imagen_inversa.thy
-- Si u ⊆ v, entonces f⁻¹[u] ⊆ f⁻¹[v].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-junio-2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si u \<subseteq> v, entonces
--    f -` u \<subseteq> f -` v
-- ------------------------------------------------------------------- *)

theory Monotonia_de_la_imagen_inversa
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
proof (rule subsetI)
  fix x
  assume "x \<in> f -` u"
  then have "f x \<in> u"
    by (rule vimageD)
  then have "f x \<in> v"
    using \<open>u \<subseteq> v\<close> by (rule set_rev_mp)
  then show "x \<in> f -` v"
    by (simp only: vimage_eq)
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
proof
  fix x
  assume "x \<in> f -` u"
  then have "f x \<in> u"
    by simp
  then have "f x \<in> v"
    using \<open>u \<subseteq> v\<close> by (rule set_rev_mp)
  then show "x \<in> f -` v"
    by simp
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
  using assms
  by (simp only: vimage_mono)

(* 4\<ordfeminine> demostración *)
lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
  using assms
  by blast

end
