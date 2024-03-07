(* Interseccion_de_intersecciones.thy
   (\<Inter> i, A i \<inter> B i) = (\<Inter> i, A i) \<inter> (\<Inter> i, B i)
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 8-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Demostrar que
      (\<Inter> i, A i \<inter> B i) = (\<Inter> i, A i) \<inter> (\<Inter> i, B i)
  ------------------------------------------------------------------- *)

theory Interseccion_de_intersecciones
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "(\<Inter> i \<in> I. A i \<inter> B i) = (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
proof (rule equalityI)
  show "(\<Inter> i \<in> I. A i \<inter> B i) \<subseteq> (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
  proof (rule subsetI)
    fix x
    assume h1 : "x \<in> (\<Inter> i \<in> I. A i \<inter> B i)"
    have "x \<in> (\<Inter> i \<in> I. A i)"
    proof (rule INT_I)
      fix i
      assume "i \<in> I"
      with h1 have "x \<in> A i \<inter> B i"
        by (rule INT_D)
      then show "x \<in> A i"
        by (rule IntD1)
    qed
    moreover
    have "x \<in> (\<Inter> i \<in> I. B i)"
    proof (rule INT_I)
      fix i
      assume "i \<in> I"
      with h1 have "x \<in> A i \<inter> B i"
        by (rule INT_D)
      then show "x \<in> B i"
        by (rule IntD2)
    qed
    ultimately show "x \<in> (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
      by (rule IntI)
  qed
next
  show "(\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i) \<subseteq> (\<Inter> i \<in> I. A i \<inter> B i)"
  proof (rule subsetI)
    fix x
    assume h2 : "x \<in> (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
    show "x \<in> (\<Inter> i \<in> I. A i \<inter> B i)"
    proof (rule INT_I)
      fix i
      assume "i \<in> I"
      have "x \<in> A i"
      proof -
        have "x \<in> (\<Inter> i \<in> I. A i)"
          using h2 by (rule IntD1)
        then show "x \<in> A i"
          using \<open>i \<in> I\<close> by (rule INT_D)
      qed
      moreover
      have "x \<in> B i"
      proof -
        have "x \<in> (\<Inter> i \<in> I. B i)"
          using h2 by (rule IntD2)
        then show "x \<in> B i"
          using \<open>i \<in> I\<close> by (rule INT_D)
      qed
      ultimately show "x \<in> A i \<inter> B i"
        by (rule IntI)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "(\<Inter> i \<in> I. A i \<inter> B i) = (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
proof
  show "(\<Inter> i \<in> I. A i \<inter> B i) \<subseteq> (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
  proof
    fix x
    assume h1 : "x \<in> (\<Inter> i \<in> I. A i \<inter> B i)"
    have "x \<in> (\<Inter> i \<in> I. A i)"
    proof
      fix i
      assume "i \<in> I"
      then show "x \<in> A i"
        using h1 by simp
    qed
    moreover
    have "x \<in> (\<Inter> i \<in> I. B i)"
    proof
      fix i
      assume "i \<in> I"
      then show "x \<in> B i"
        using h1 by simp
    qed
    ultimately show "x \<in> (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
      by simp
  qed
next
  show "(\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i) \<subseteq> (\<Inter> i \<in> I. A i \<inter> B i)"
  proof
    fix x
    assume h2 : "x \<in> (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
    show "x \<in> (\<Inter> i \<in> I. A i \<inter> B i)"
    proof
      fix i
      assume "i \<in> I"
      then have "x \<in> A i"
        using h2 by simp
      moreover
      have "x \<in> B i"
        using \<open>i \<in> I\<close> h2 by simp
      ultimately show "x \<in> A i \<inter> B i"
        by simp
    qed
qed
qed

(* 3\<ordfeminine> demostración *)
lemma "(\<Inter> i \<in> I. A i \<inter> B i) = (\<Inter> i \<in> I. A i) \<inter> (\<Inter> i \<in> I. B i)"
  by auto

end
