(* Diferencia_de_diferencia_de_conjuntos.thy
   Diferencia de diferencia de conjuntos
   José A. Alonso Jiménez
   Sevilla, 22 de febrero de 2024
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
-- Demostrar que
--    (s - t) - u \<subseteq> s - (t \<union> u)
-- ------------------------------------------------------------------ *)

theory Diferencia_de_diferencia_de_conjuntos
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "(s - t) - u \<subseteq> s - (t \<union> u)"
proof (rule subsetI)
  fix x
  assume hx : "x \<in> (s - t) - u"
  then show "x \<in> s - (t \<union> u)"
  proof (rule DiffE)
    assume xst : "x \<in> s - t"
    assume xnu : "x \<notin> u"
    note xst
    then show "x \<in> s - (t \<union> u)"
    proof (rule DiffE)
      assume xs : "x \<in> s"
      assume xnt : "x \<notin> t"
      have xntu : "x \<notin> t \<union> u"
      proof (rule notI)
        assume xtu : "x \<in> t \<union> u"
        then show False
        proof (rule UnE)
          assume xt : "x \<in> t"
          with xnt show False
            by (rule notE)
        next
          assume xu : "x \<in> u"
          with xnu show False
            by (rule notE)
        qed
      qed
      show "x \<in> s - (t \<union> u)"
        using xs xntu by (rule DiffI)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "(s - t) - u \<subseteq> s - (t \<union> u)"
proof
  fix x
  assume hx : "x \<in> (s - t) - u"
  then have xst : "x \<in> (s - t)"
    by simp
  then have xs : "x \<in> s"
    by simp
  have xnt : "x \<notin> t"
    using xst by simp
  have xnu : "x \<notin> u"
    using hx by simp
  have xntu : "x \<notin> t \<union> u"
    using xnt xnu by simp
  then show "x \<in> s - (t \<union> u)"
    using xs by simp
qed

(* 3\<ordfeminine> demostración *)
lemma "(s - t) - u \<subseteq> s - (t \<union> u)"
proof
  fix x
  assume "x \<in> (s - t) - u"
  then show "x \<in> s - (t \<union> u)"
     by simp
qed

(* 4\<ordfeminine> demostración *)
lemma "(s - t) - u \<subseteq> s - (t \<union> u)"
by auto

end
