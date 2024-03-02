(* Diferencia_de_union_e_interseccion.thy
   Diferencia de unión e intersección
   José A. Alonso Jiménez
   Sevilla, 5 de marzo de 2024
   ---------------------------------------------------------------------
*)

(* ---------------------------------------------------------------------
  Demostrar que
     (s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)
  ------------------------------------------------------------------- *)

theory Diferencia_de_union_e_interseccion
imports Main
begin

(* 1 demostración *)
lemma "(s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)"
proof (rule equalityI)
  show "(s - t) \<union> (t - s) \<subseteq> (s \<union> t) - (s \<inter> t)"
  proof (rule subsetI)
    fix x
    assume "x \<in> (s - t) \<union> (t - s)"
    then show "x \<in> (s \<union> t) - (s \<inter> t)"
    proof (rule UnE)
      assume "x \<in> s - t"
      then show "x \<in> (s \<union> t) - (s \<inter> t)"
      proof (rule DiffE)
        assume "x \<in> s"
        assume "x \<notin> t"
        have "x \<in> s \<union> t"
          using \<open>x \<in> s\<close> by (simp only: UnI1)
        moreover
        have "x \<notin> s \<inter> t"
        proof (rule notI)
          assume "x \<in> s \<inter> t"
          then have "x \<in> t"
            by (simp only: IntD2)
          with \<open>x \<notin> t\<close> show False
            by (rule notE)
        qed
        ultimately show "x \<in> (s \<union> t) - (s \<inter> t)"
          by (rule DiffI)
      qed
    next
      assume "x \<in> t - s"
      then show "x \<in> (s \<union> t) - (s \<inter> t)"
      proof (rule DiffE)
        assume "x \<in> t"
        assume "x \<notin> s"
        have "x \<in> s \<union> t"
          using \<open>x \<in> t\<close> by (simp only: UnI2)
        moreover
        have "x \<notin> s \<inter> t"
        proof (rule notI)
          assume "x \<in> s \<inter> t"
          then have "x \<in> s"
            by (simp only: IntD1)
          with \<open>x \<notin> s\<close> show False
            by (rule notE)
        qed
        ultimately show "x \<in> (s \<union> t) - (s \<inter> t)"
          by (rule DiffI)
      qed
    qed
  qed
next
  show "(s \<union> t) - (s \<inter> t) \<subseteq> (s - t) \<union> (t - s)"
  proof (rule subsetI)
    fix x
    assume "x \<in> (s \<union> t) - (s \<inter> t)"
    then show "x \<in> (s - t) \<union> (t - s)"
    proof (rule DiffE)
      assume "x \<in> s \<union> t"
      assume "x \<notin> s \<inter> t"
      note \<open>x \<in> s \<union> t\<close>
      then show "x \<in> (s - t) \<union> (t - s)"
      proof (rule UnE)
        assume "x \<in> s"
        have "x \<notin> t"
        proof (rule notI)
          assume "x \<in> t"
          with \<open>x \<in> s\<close> have "x \<in> s \<inter> t"
            by (rule IntI)
          with \<open>x \<notin> s \<inter> t\<close> show False
            by (rule notE)
        qed
        with \<open>x \<in> s\<close> have "x \<in> s - t"
          by (rule DiffI)
        then show "x \<in> (s - t) \<union> (t - s)"
          by (simp only: UnI1)
      next
        assume "x \<in> t"
        have "x \<notin> s"
        proof (rule notI)
          assume "x \<in> s"
          then have "x \<in> s \<inter> t"
            using \<open>x \<in> t\<close> by (rule IntI)
          with \<open>x \<notin> s \<inter> t\<close> show False
            by (rule notE)
        qed
        with \<open>x \<in> t\<close> have "x \<in> t - s"
          by (rule DiffI)
        then show "x \<in> (s - t) \<union> (t - s)"
          by (rule UnI2)
      qed
    qed
  qed
qed

(* 2 demostración *)
lemma "(s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)"
proof
  show "(s - t) \<union> (t - s) \<subseteq> (s \<union> t) - (s \<inter> t)"
  proof
    fix x
    assume "x \<in> (s - t) \<union> (t - s)"
    then show "x \<in> (s \<union> t) - (s \<inter> t)"
    proof
      assume "x \<in> s - t"
      then show "x \<in> (s \<union> t) - (s \<inter> t)"
      proof
        assume "x \<in> s"
        assume "x \<notin> t"
        have "x \<in> s \<union> t"
          using \<open>x \<in> s\<close> by simp
        moreover
        have "x \<notin> s \<inter> t"
        proof
          assume "x \<in> s \<inter> t"
          then have "x \<in> t"
            by simp
          with \<open>x \<notin> t\<close> show False
            by simp
        qed
        ultimately show "x \<in> (s \<union> t) - (s \<inter> t)"
          by simp
      qed
    next
      assume "x \<in> t - s"
      then show "x \<in> (s \<union> t) - (s \<inter> t)"
      proof
        assume "x \<in> t"
        assume "x \<notin> s"
        have "x \<in> s \<union> t"
          using \<open>x \<in> t\<close> by simp
        moreover
        have "x \<notin> s \<inter> t"
        proof
          assume "x \<in> s \<inter> t"
          then have "x \<in> s"
            by simp
          with \<open>x \<notin> s\<close> show False
            by simp
        qed
        ultimately show "x \<in> (s \<union> t) - (s \<inter> t)"
          by simp
      qed
    qed
  qed
next
  show "(s \<union> t) - (s \<inter> t) \<subseteq> (s - t) \<union> (t - s)"
  proof
    fix x
    assume "x \<in> (s \<union> t) - (s \<inter> t)"
    then show "x \<in> (s - t) \<union> (t - s)"
    proof
      assume "x \<in> s \<union> t"
      assume "x \<notin> s \<inter> t"
      note \<open>x \<in> s \<union> t\<close>
      then show "x \<in> (s - t) \<union> (t - s)"
      proof
        assume "x \<in> s"
        have "x \<notin> t"
        proof
          assume "x \<in> t"
          with \<open>x \<in> s\<close> have "x \<in> s \<inter> t"
            by simp
          with \<open>x \<notin> s \<inter> t\<close> show False
            by simp
        qed
        with \<open>x \<in> s\<close> have "x \<in> s - t"
          by simp
        then show "x \<in> (s - t) \<union> (t - s)"
          by simp
      next
        assume "x \<in> t"
        have "x \<notin> s"
        proof
          assume "x \<in> s"
          then have "x \<in> s \<inter> t"
            using \<open>x \<in> t\<close> by simp
          with \<open>x \<notin> s \<inter> t\<close> show False
            by simp
        qed
        with \<open>x \<in> t\<close> have "x \<in> t - s"
          by simp
        then show "x \<in> (s - t) \<union> (t - s)"
          by simp
      qed
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "(s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)"
proof
  show "(s - t) \<union> (t - s) \<subseteq> (s \<union> t) - (s \<inter> t)"
  proof
    fix x
    assume "x \<in> (s - t) \<union> (t - s)"
    then show "x \<in> (s \<union> t) - (s \<inter> t)"
    proof
      assume "x \<in> s - t"
      then show "x \<in> (s \<union> t) - (s \<inter> t)" by simp
    next
      assume "x \<in> t - s"
      then show "x \<in> (s \<union> t) - (s \<inter> t)" by simp
    qed
  qed
next
  show "(s \<union> t) - (s \<inter> t) \<subseteq> (s - t) \<union> (t - s)"
  proof
    fix x
    assume "x \<in> (s \<union> t) - (s \<inter> t)"
    then show "x \<in> (s - t) \<union> (t - s)"
    proof
      assume "x \<in> s \<union> t"
      assume "x \<notin> s \<inter> t"
      note \<open>x \<in> s \<union> t\<close>
      then show "x \<in> (s - t) \<union> (t - s)"
      proof
        assume "x \<in> s"
        then show "x \<in> (s - t) \<union> (t - s)"
          using \<open>x \<notin> s \<inter> t\<close> by simp
      next
        assume "x \<in> t"
        then show "x \<in> (s - t) \<union> (t - s)"
          using \<open>x \<notin> s \<inter> t\<close> by simp
      qed
    qed
  qed
qed

(* 4\<ordfeminine> demostración *)

lemma "(s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)"
proof
  show "(s - t) \<union> (t - s) \<subseteq> (s \<union> t) - (s \<inter> t)"
  proof
    fix x
    assume "x \<in> (s - t) \<union> (t - s)"
    then show "x \<in> (s \<union> t) - (s \<inter> t)" by auto
  qed
next
  show "(s \<union> t) - (s \<inter> t) \<subseteq> (s - t) \<union> (t - s)"
  proof
    fix x
    assume "x \<in> (s \<union> t) - (s \<inter> t)"
    then show "x \<in> (s - t) \<union> (t - s)" by auto
  qed
qed

(* 5\<ordfeminine> demostración *)

lemma "(s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)"
proof
  show "(s - t) \<union> (t - s) \<subseteq> (s \<union> t) - (s \<inter> t)" by auto
next
  show "(s \<union> t) - (s \<inter> t) \<subseteq> (s - t) \<union> (t - s)" by auto
qed

(* 6\<ordfeminine> demostración *)

lemma "(s - t) \<union> (t - s) = (s \<union> t) - (s \<inter> t)"
  by auto

end
