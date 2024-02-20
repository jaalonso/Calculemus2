(* Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.thy
   Propiedad semidistributiva de la intersección sobre la unión
   José A. Alonso Jiménez
   Sevilla, 18 de mayo de 2021
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
-- Demostrar que
--    s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)
-- ------------------------------------------------------------------ *)

theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)"
proof (rule subsetI)
  fix x
  assume hx : "x \<in> s \<inter> (t \<union> u)"
  then have xs : "x \<in> s"
    by (simp only: IntD1)
  have xtu: "x \<in> t \<union> u"
    using hx 
    by (simp only: IntD2)
  then have "x \<in> t \<or> x \<in> u"
    by (simp only: Un_iff)
  then show " x \<in> s \<inter> t \<union> s \<inter> u"
  proof (rule disjE)
    assume xt : "x \<in> t"
    have xst : "x \<in> s \<inter> t"
      using xs xt by (simp only: Int_iff)
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by (simp only: UnI1)
  next
    assume xu : "x \<in> u"
    have xst : "x \<in> s \<inter> u"
      using xs xu by (simp only: Int_iff)
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by (simp only: UnI2)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)"
proof
  fix x
  assume hx : "x \<in> s \<inter> (t \<union> u)"
  then have xs : "x \<in> s"
    by simp
  have xtu: "x \<in> t \<union> u"
    using hx 
    by simp
  then have "x \<in> t \<or> x \<in> u"
    by simp
  then show " x \<in> s \<inter> t \<union> s \<inter> u"
  proof
    assume xt : "x \<in> t"
    have xst : "x \<in> s \<inter> t"
      using xs xt 
      by simp
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by simp
  next
    assume xu : "x \<in> u"
    have xst : "x \<in> s \<inter> u"
      using xs xu 
      by simp
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)"
proof (rule subsetI)
  fix x
  assume hx : "x \<in> s \<inter> (t \<union> u)"
  then have xs : "x \<in> s"
    by (simp only: IntD1)
  have xtu: "x \<in> t \<union> u"
    using hx 
    by (simp only: IntD2)
  then show " x \<in> s \<inter> t \<union> s \<inter> u"
  proof (rule UnE)
    assume xt : "x \<in> t"
    have xst : "x \<in> s \<inter> t"
      using xs xt 
      by (simp only: Int_iff)
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by (simp only: UnI1)
  next
    assume xu : "x \<in> u"
    have xst : "x \<in> s \<inter> u"
      using xs xu 
      by (simp only: Int_iff)
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by (simp only: UnI2)
  qed
qed

(* 4\<ordfeminine> demostración *)
lemma "s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)"
proof
  fix x
  assume hx : "x \<in> s \<inter> (t \<union> u)"
  then have xs : "x \<in> s"
    by simp
  have xtu: "x \<in> t \<union> u"
    using hx 
    by simp
  then show " x \<in> s \<inter> t \<union> s \<inter> u"
  proof (rule UnE)
    assume xt : "x \<in> t"
    have xst : "x \<in> s \<inter> t"
      using xs xt 
      by simp
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by simp
  next
    assume xu : "x \<in> u"
    have xst : "x \<in> s \<inter> u"
      using xs xu by simp
    then show "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
      by simp
  qed
qed

(* 5\<ordfeminine> demostración *)
lemma "s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)"
by (simp only: Int_Un_distrib)

(* 6\<ordfeminine> demostración *)
lemma "s \<inter> (t \<union> u) \<subseteq> (s \<inter> t) \<union> (s \<inter> u)"
by auto

end
