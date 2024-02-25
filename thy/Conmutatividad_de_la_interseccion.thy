(* Conmutatividad_de_la_interseccion.thy
   Conmutatividad de la intersección.
   José A. Alonso Jiménez
   Sevilla, 27 de febrero de 2024
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
-- Demostrar que
--    s \<inter> t = t \<inter> s
-- ------------------------------------------------------------------ *)

theory Conmutatividad_de_la_interseccion
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
proof (rule set_eqI)
  fix x
  show "x \<in> s \<inter> t \<longleftrightarrow> x \<in> t \<inter> s"
  proof (rule iffI)
    assume h : "x \<in> s \<inter> t"
    then have xs : "x \<in> s"
      by (simp only: IntD1)
    have xt : "x \<in> t"
      using h by (simp only: IntD2)
    then show "x \<in> t \<inter> s"
      using xs by (rule IntI)
  next
    assume h : "x \<in> t \<inter> s"
    then have xt : "x \<in> t"
      by (simp only: IntD1)
    have xs : "x \<in> s"
      using h by (simp only: IntD2)
    then show "x \<in> s \<inter> t"
      using xt by (rule IntI)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
proof (rule set_eqI)
  fix x
  show "x \<in> s \<inter> t \<longleftrightarrow> x \<in> t \<inter> s"
  proof
    assume h : "x \<in> s \<inter> t"
    then have xs : "x \<in> s"
      by simp
    have xt : "x \<in> t"
      using h by simp
    then show "x \<in> t \<inter> s"
      using xs by simp
  next
    assume h : "x \<in> t \<inter> s"
    then have xt : "x \<in> t"
      by simp
    have xs : "x \<in> s"
      using h by simp
    then show "x \<in> s \<inter> t"
      using xt by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
proof (rule equalityI)
  show "s \<inter> t \<subseteq> t \<inter> s"
  proof (rule subsetI)
    fix x
    assume h : "x \<in> s \<inter> t"
    then have xs : "x \<in> s"
      by (simp only: IntD1)
    have xt : "x \<in> t"
      using h by (simp only: IntD2)
    then show "x \<in> t \<inter> s"
      using xs by (rule IntI)
  qed
next
  show "t \<inter> s \<subseteq> s \<inter> t"
  proof (rule subsetI)
    fix x
    assume h : "x \<in> t \<inter> s"
    then have xt : "x \<in> t"
      by (simp only: IntD1)
    have xs : "x \<in> s"
      using h by (simp only: IntD2)
    then show "x \<in> s \<inter> t"
      using xt by (rule IntI)
  qed
qed

(* 4\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
proof
  show "s \<inter> t \<subseteq> t \<inter> s"
  proof
    fix x
    assume h : "x \<in> s \<inter> t"
    then have xs : "x \<in> s"
      by simp
    have xt : "x \<in> t"
      using h by simp
    then show "x \<in> t \<inter> s"
      using xs by simp
  qed
next
  show "t \<inter> s \<subseteq> s \<inter> t"
  proof
    fix x
    assume h : "x \<in> t \<inter> s"
    then have xt : "x \<in> t"
      by simp
    have xs : "x \<in> s"
      using h by simp
    then show "x \<in> s \<inter> t"
      using xt by simp
  qed
qed

(* 5\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
proof
  show "s \<inter> t \<subseteq> t \<inter> s"
  proof
    fix x
    assume "x \<in> s \<inter> t"
    then show "x \<in> t \<inter> s"
      by simp
  qed
next
  show "t \<inter> s \<subseteq> s \<inter> t"
  proof
    fix x
    assume "x \<in> t \<inter> s"
    then show "x \<in> s \<inter> t"
      by simp
  qed
qed

(* 6\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
by (fact Int_commute)

(* 7\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
by (fact inf_commute)

(* 8\<ordfeminine> demostración *)
lemma "s \<inter> t = t \<inter> s"
by auto

end
