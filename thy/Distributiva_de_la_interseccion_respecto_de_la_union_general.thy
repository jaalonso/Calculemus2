(* Distributiva_de_la_interseccion_respecto_de_la_union_general.lean
   s \<inter> (\<Union> i, A i) = \<Union> i, (A i \<inter> s)
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 7-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Demostrar que
      s \<inter> (\<Union> i, A i) = \<Union> i, (A i \<inter> s)
  ------------------------------------------------------------------- *)

theory Distributiva_de_la_interseccion_respecto_de_la_union_general
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s \<inter> (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. (A i \<inter> s))"
proof (rule equalityI)
  show "s \<inter> (\<Union> i \<in> I. A i) \<subseteq> (\<Union> i \<in> I. (A i \<inter> s))"
  proof (rule subsetI)
    fix x
    assume "x \<in> s \<inter> (\<Union> i \<in> I. A i)"
    then have "x \<in> s"
      by (simp only: IntD1)
    have "x \<in> (\<Union> i \<in> I. A i)"
      using \<open>x \<in> s \<inter> (\<Union> i \<in> I. A i)\<close> by (simp only: IntD2)
    then show "x \<in> (\<Union> i \<in> I. (A i \<inter> s))"
    proof (rule UN_E)
      fix i
      assume "i \<in> I"
      assume "x \<in> A i"
      then have "x \<in> A i \<inter> s"
        using \<open>x \<in> s\<close> by (rule IntI)
      with \<open>i \<in> I\<close> show "x \<in> (\<Union> i \<in> I. (A i \<inter> s))"
        by (rule UN_I)
    qed
  qed
next
  show "(\<Union> i \<in> I. (A i \<inter> s)) \<subseteq> s \<inter> (\<Union> i \<in> I. A i)"
  proof (rule subsetI)
    fix x
    assume "x \<in> (\<Union> i \<in> I. A i \<inter> s)"
    then show "x \<in> s \<inter> (\<Union> i \<in> I. A i)"
    proof (rule UN_E)
      fix i
      assume "i \<in> I"
      assume "x \<in> A i \<inter> s"
      then have "x \<in> A i"
        by (rule IntD1)
      have "x \<in> s"
        using \<open>x \<in> A i \<inter> s\<close> by (rule IntD2)
      moreover
      have "x \<in> (\<Union> i \<in> I. A i)"
        using \<open>i \<in> I\<close> \<open>x \<in> A i\<close> by (rule UN_I)
      ultimately show "x \<in> s \<inter> (\<Union> i \<in> I. A i)"
        by (rule IntI)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "s \<inter> (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. (A i \<inter> s))"
proof
  show "s \<inter> (\<Union> i \<in> I. A i) \<subseteq> (\<Union> i \<in> I. (A i \<inter> s))"
  proof
    fix x
    assume "x \<in> s \<inter> (\<Union> i \<in> I. A i)"
    then have "x \<in> s"
      by simp
    have "x \<in> (\<Union> i \<in> I. A i)"
      using \<open>x \<in> s \<inter> (\<Union> i \<in> I. A i)\<close> by simp
    then show "x \<in> (\<Union> i \<in> I. (A i \<inter> s))"
    proof
      fix i
      assume "i \<in> I"
      assume "x \<in> A i"
      then have "x \<in> A i \<inter> s"
        using \<open>x \<in> s\<close> by simp
      with \<open>i \<in> I\<close> show "x \<in> (\<Union> i \<in> I. (A i \<inter> s))"
        by (rule UN_I)
    qed
  qed
next
  show "(\<Union> i \<in> I. (A i \<inter> s)) \<subseteq> s \<inter> (\<Union> i \<in> I. A i)"
  proof
    fix x
    assume "x \<in> (\<Union> i \<in> I. A i \<inter> s)"
    then show "x \<in> s \<inter> (\<Union> i \<in> I. A i)"
    proof
      fix i
      assume "i \<in> I"
      assume "x \<in> A i \<inter> s"
      then have "x \<in> A i"
        by simp
      have "x \<in> s"
        using \<open>x \<in> A i \<inter> s\<close> by simp
      moreover
      have "x \<in> (\<Union> i \<in> I. A i)"
        using \<open>i \<in> I\<close> \<open>x \<in> A i\<close> by (rule UN_I)
      ultimately show "x \<in> s \<inter> (\<Union> i \<in> I. A i)"
        by simp
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "s \<inter> (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. (A i \<inter> s))"
  by auto

end
