(* Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.lean
   (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
   José A. Alonso Jiménez
   Sevilla, 22 de febrero de 2024
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
-- Demostrar que
--    (s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)
-- ------------------------------------------------------------------ *)

theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "(s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)"
proof (rule subsetI)
  fix x
  assume "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
  then show "x \<in> s \<inter> (t \<union> u)"
  proof (rule UnE)
    assume xst : "x \<in> s \<inter> t"
    then have xs : "x \<in> s"
      by (simp only: IntD1)
    have xt : "x \<in> t"
      using xst by (simp only: IntD2)
    then have xtu : "x \<in> t \<union> u"
      by (simp only: UnI1)
    show "x \<in> s \<inter> (t \<union> u)"
      using xs xtu by (simp only: IntI)
  next
    assume xsu : "x \<in> s \<inter> u"
    then have xs : "x \<in> s"
      by (simp only: IntD1)
    have xt : "x \<in> u"
      using xsu by (simp only: IntD2)
    then have xtu : "x \<in> t \<union> u"
      by (simp only: UnI2)
    show "x \<in> s \<inter> (t \<union> u)"
      using xs xtu by (simp only: IntI)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "(s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)"
proof
  fix x
  assume "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
  then show "x \<in> s \<inter> (t \<union> u)"
  proof
    assume xst : "x \<in> s \<inter> t"
    then have xs : "x \<in> s"
      by simp
    have xt : "x \<in> t"
      using xst by simp
    then have xtu : "x \<in> t \<union> u"
      by simp
    show "x \<in> s \<inter> (t \<union> u)"
      using xs xtu by simp
  next
    assume xsu : "x \<in> s \<inter> u"
    then have xs : "x \<in> s"
      by (simp only: IntD1)
    have xt : "x \<in> u"
      using xsu by simp
    then have xtu : "x \<in> t \<union> u"
      by simp
    show "x \<in> s \<inter> (t \<union> u)"
      using xs xtu by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "(s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)"
proof
  fix x
  assume "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
  then show "x \<in> s \<inter> (t \<union> u)"
  proof
    assume "x \<in> s \<inter> t"
    then show "x \<in> s \<inter> (t \<union> u)"
      by simp
  next
    assume "x \<in> s \<inter> u"
    then show "x \<in> s \<inter> (t \<union> u)"
      by simp
  qed
qed

(* 4\<ordfeminine> demostración *)
lemma "(s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)"
proof
  fix x
  assume "x \<in> (s \<inter> t) \<union> (s \<inter> u)"
  then show "x \<in> s \<inter> (t \<union> u)"
    by auto
qed

(* 5\<ordfeminine> demostración *)
lemma "(s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)"
by auto

(* 6\<ordfeminine> demostración *)
lemma "(s \<inter> t) \<union> (s \<inter> u) \<subseteq> s \<inter> (t \<union> u)"
by (simp only: distrib_inf_le)

end
