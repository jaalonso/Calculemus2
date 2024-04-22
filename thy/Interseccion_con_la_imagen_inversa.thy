(* Interseccion_con_la_imagen.thy
-- Intersección con la imagen.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    (f ` s) \<inter> v = f ` (s \<inter> f -` v)
-- ------------------------------------------------------------------ *)

theory Interseccion_con_la_imagen_inversa
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "(f ` s) \<inter> v = f ` (s \<inter> f -` v)"
proof (rule equalityI)
  show "(f ` s) \<inter> v \<subseteq> f ` (s \<inter> f -` v)"
  proof (rule subsetI)
    fix y
    assume "y \<in> (f ` s) \<inter> v"
    then show "y \<in> f ` (s \<inter> f -` v)"
    proof (rule IntE)
      assume "y \<in> v"
      assume "y \<in> f ` s"
      then show "y \<in> f ` (s \<inter> f -` v)"
      proof (rule imageE)
        fix x
        assume "x \<in> s"
        assume "y = f x"
        then have "f x \<in> v"
          using \<open>y \<in> v\<close> by (rule subst)
        then have "x \<in> f -` v"
          by (rule vimageI2)
        with \<open>x \<in> s\<close> have "x \<in> s \<inter> f -` v"
          by (rule IntI)
        then have "f x \<in> f ` (s \<inter> f -` v)"
          by (rule imageI)
        with \<open>y = f x\<close> show "y \<in> f ` (s \<inter> f -` v)"
          by (rule ssubst)
      qed
    qed
  qed
next
  show "f ` (s \<inter> f -` v) \<subseteq> (f ` s) \<inter> v"
  proof (rule subsetI)
    fix y
    assume "y \<in> f ` (s \<inter> f -` v)"
    then show "y \<in> (f ` s) \<inter> v"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume hx : "x \<in> s \<inter> f -` v"
      have "y \<in> f ` s"
      proof -
        have "x \<in> s"
          using hx by (rule IntD1)
        then have "f x \<in> f ` s"
          by (rule imageI)
        with \<open>y = f x\<close> show "y \<in> f ` s"
          by (rule ssubst)
      qed
      moreover
      have "y \<in> v"
      proof -
        have "x \<in> f -` v"
          using hx by (rule IntD2)
        then have "f x \<in> v"
          by (rule vimageD)
        with \<open>y = f x\<close> show "y \<in> v"
          by (rule ssubst)
      qed
      ultimately show "y \<in> (f ` s) \<inter> v"
        by (rule IntI)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "(f ` s) \<inter> v = f ` (s \<inter> f -` v)"
proof
  show "(f ` s) \<inter> v \<subseteq> f ` (s \<inter> f -` v)"
  proof
    fix y
    assume "y \<in> (f ` s) \<inter> v"
    then show "y \<in> f ` (s \<inter> f -` v)"
    proof
      assume "y \<in> v"
      assume "y \<in> f ` s"
      then show "y \<in> f ` (s \<inter> f -` v)"
      proof
        fix x
        assume "x \<in> s"
        assume "y = f x"
        then have "f x \<in> v" using \<open>y \<in> v\<close> by simp
        then have "x \<in> f -` v" by simp
        with \<open>x \<in> s\<close> have "x \<in> s \<inter> f -` v" by simp
        then have "f x \<in> f ` (s \<inter> f -` v)" by simp
        with \<open>y = f x\<close> show "y \<in> f ` (s \<inter> f -` v)" by simp
      qed
    qed
  qed
next
  show "f ` (s \<inter> f -` v) \<subseteq> (f ` s) \<inter> v"
  proof
    fix y
    assume "y \<in> f ` (s \<inter> f -` v)"
    then show "y \<in> (f ` s) \<inter> v"
    proof
      fix x
      assume "y = f x"
      assume hx : "x \<in> s \<inter> f -` v"
      have "y \<in> f ` s"
      proof -
        have "x \<in> s" using hx by simp
        then have "f x \<in> f ` s" by simp
        with \<open>y = f x\<close> show "y \<in> f ` s" by simp
      qed
      moreover
      have "y \<in> v"
      proof -
        have "x \<in> f -` v" using hx by simp
        then have "f x \<in> v" by simp
        with \<open>y = f x\<close> show "y \<in> v" by simp
      qed
      ultimately show "y \<in> (f ` s) \<inter> v" by simp
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "(f ` s) \<inter> v = f ` (s \<inter> f -` v)"
proof
  show "(f ` s) \<inter> v \<subseteq> f ` (s \<inter> f -` v)"
  proof
    fix y
    assume "y \<in> (f ` s) \<inter> v"
    then show "y \<in> f ` (s \<inter> f -` v)"
    proof
      assume "y \<in> v"
      assume "y \<in> f ` s"
      then show "y \<in> f ` (s \<inter> f -` v)"
      proof
        fix x
        assume "x \<in> s"
        assume "y = f x"
        then show "y \<in> f ` (s \<inter> f -` v)"
          using \<open>x \<in> s\<close> \<open>y \<in> v\<close> by simp
      qed
    qed
  qed
next
  show "f ` (s \<inter> f -` v) \<subseteq> (f ` s) \<inter> v"
  proof
    fix y
    assume "y \<in> f ` (s \<inter> f -` v)"
    then show "y \<in> (f ` s) \<inter> v"
    proof
      fix x
      assume "y = f x"
      assume hx : "x \<in> s \<inter> f -` v"
      then have "y \<in> f ` s" using \<open>y = f x\<close> by simp
      moreover
      have "y \<in> v" using hx \<open>y = f x\<close> by simp
      ultimately show "y \<in> (f ` s) \<inter> v" by simp
    qed
  qed
qed

(* 4\<ordfeminine> demostración *)

lemma "(f ` s) \<inter> v = f ` (s \<inter> f -` v)"
  by auto

end
