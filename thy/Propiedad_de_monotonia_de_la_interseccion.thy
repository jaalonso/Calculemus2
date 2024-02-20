(* Propiedad_de_monotonia_de_la_interseccion.lean
   Si s \<subseteq> t, entonces s \<inter> u \<subseteq> t \<inter> u.
   José A. Alonso Jiménez
   Sevilla, 20 de febrero de 2024
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
-- Demostrar que si
--    s \<subseteq> t
-- entonces
--    s \<inter> u \<subseteq> t \<inter> u
-- ------------------------------------------------------------------ *)

theory Propiedad_de_monotonia_de_la_interseccion
imports Main
begin

(* 1\<ordfeminine> solución *)
lemma
  assumes "s \<subseteq> t"
  shows   "s \<inter> u \<subseteq> t \<inter> u"
proof (rule subsetI)
  fix x
  assume hx: "x \<in> s \<inter> u"
  have xs: "x \<in> s"
    using hx
    by (simp only: IntD1)
  then have xt: "x \<in> t"
    using assms
    by (simp only: subset_eq)
  have xu: "x \<in> u"
    using hx
    by (simp only: IntD2)
  show "x \<in> t \<inter> u"
    using xt xu
    by (simp only: Int_iff)
qed

(* 2 solución *)
lemma
  assumes "s \<subseteq> t"
  shows   "s \<inter> u \<subseteq> t \<inter> u"
proof
  fix x
  assume hx: "x \<in> s \<inter> u"
  have xs: "x \<in> s"
    using hx
    by simp
  then have xt: "x \<in> t"
    using assms
    by auto
  have xu: "x \<in> u"
    using hx
    by simp
  show "x \<in> t \<inter> u"
    using xt xu
    by simp
qed

(* 3\<ordfeminine> solución *)
lemma
  assumes "s \<subseteq> t"
  shows   "s \<inter> u \<subseteq> t \<inter> u"
using assms
by auto

(* 4\<ordfeminine> solución *)
lemma
  "s \<subseteq> t \<Longrightarrow> s \<inter> u \<subseteq> t \<inter> u"
by auto

end
