(* La_paradoja_del_barbero.lean
-- La paradoja del barbero.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar la paradoja del barbero https://bit.ly/3eWyvVw es decir,
-- que no existe un hombre que afeite a todos los que no se afeitan a sí
-- mismo y sólo a los que no se afeitan a sí mismo.
-- ------------------------------------------------------------------ *)

theory La_paradoja_del_barbero
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  "\<not>(\<exists> x::'H. \<forall> y::'H. afeita x y \<longleftrightarrow> \<not> afeita y y)"
proof (rule notI)
  assume "\<exists> x. \<forall> y. afeita x y \<longleftrightarrow> \<not> afeita y y"
  then obtain b where "\<forall> y. afeita b y \<longleftrightarrow> \<not> afeita y y"
    by (rule exE)
  then have h : "afeita b b \<longleftrightarrow> \<not> afeita b b"
    by (rule allE)
  show False
  proof (cases "afeita b b")
    assume "afeita b b"
    then have "\<not> afeita b b"
      using h by (rule rev_iffD1)
    then show False
      using \<open>afeita b b\<close> by (rule notE)
  next
    assume "\<not> afeita b b"
    then have "afeita b b"
      using h by (rule rev_iffD2)
    with \<open>\<not> afeita b b\<close> show False
      by (rule notE)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  "\<not>(\<exists> x::'H. \<forall> y::'H. afeita x y \<longleftrightarrow> \<not> afeita y y)"
proof
  assume "\<exists> x. \<forall> y. afeita x y \<longleftrightarrow> \<not> afeita y y"
  then obtain b where "\<forall> y. afeita b y \<longleftrightarrow> \<not> afeita y y"
    by (rule exE)
  then have h : "afeita b b \<longleftrightarrow> \<not> afeita b b"
    by (rule allE)
  then show False
    by simp
qed

(* 3\<ordfeminine> demostración *)

lemma
  "\<not>(\<exists> x::'H. \<forall> y::'H. afeita x y \<longleftrightarrow> \<not> afeita y y)"
  by auto

end
