(* Interseccion_con_su_union.thy
   s \<inter> (s \<union> t) = s
   José A. Alonso Jiménez
   Sevilla, 28 de febrero de 2024
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
-- Demostrar que
--    s \<inter> (s \<union> t) = s
-- ------------------------------------------------------------------ *)

theory Interseccion_con_su_union
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s \<inter> (s \<union> t) = s"
proof (rule  equalityI)
  show "s \<inter> (s \<union> t) \<subseteq> s"
  proof (rule subsetI)
    fix x
    assume "x \<in> s \<inter> (s \<union> t)"
    then show "x \<in> s"
      by (simp only: IntD1)
  qed
next
  show "s \<subseteq> s \<inter> (s \<union> t)"
  proof (rule subsetI)
    fix x
    assume "x \<in> s"
    then have "x \<in> s \<union> t"
      by (simp only: UnI1)
    with \<open>x \<in> s\<close> show "x \<in> s \<inter> (s \<union> t)"
      by (rule IntI)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "s \<inter> (s \<union> t) = s"
proof
  show "s \<inter> (s \<union> t) \<subseteq> s"
  proof
    fix x
    assume "x \<in> s \<inter> (s \<union> t)"
    then show "x \<in> s"
      by simp
  qed
next
  show "s \<subseteq> s \<inter> (s \<union> t)"
  proof
    fix x
    assume "x \<in> s"
    then have "x \<in> s \<union> t"
      by simp
    then show "x \<in> s \<inter> (s \<union> t)"
      using \<open>x \<in> s\<close> by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "s \<inter> (s \<union> t) = s"
by (fact Un_Int_eq)

(* 4\<ordfeminine> demostración *)
lemma "s \<inter> (s \<union> t) = s"
by auto
