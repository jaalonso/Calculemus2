(* Union_con_la_imagen.thy
-- Unión con la imagen
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f ` (s \<union> f -` v) \<subseteq> f ` s \<union> v
-- ------------------------------------------------------------------ *)

theory Union_con_la_imagen
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f ` (s \<union> f -` v) \<subseteq> f ` s \<union> v"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` (s \<union> f -` v)"
  then show "y \<in> f ` s \<union> v"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> s \<union> f -` v"
    then show "y \<in> f ` s \<union> v"
    proof (rule UnE)
      assume "x \<in> s"
      then have "f x \<in> f ` s"
        by (rule imageI)
      with \<open>y = f x\<close> have "y \<in> f ` s"
        by (rule ssubst)
      then show "y \<in> f ` s \<union> v"
        by (rule UnI1)
    next
      assume "x \<in> f -` v"
      then have "f x \<in> v"
        by (rule vimageD)
      with \<open>y = f x\<close> have "y \<in> v"
        by (rule ssubst)
      then show "y \<in> f ` s \<union> v"
        by (rule UnI2)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f ` (s \<union> f -` v) \<subseteq> f ` s \<union> v"
proof
  fix y
  assume "y \<in> f ` (s \<union> f -` v)"
  then show "y \<in> f ` s \<union> v"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s \<union> f -` v"
    then show "y \<in> f ` s \<union> v"
    proof
      assume "x \<in> s"
      then have "f x \<in> f ` s" by simp
      with \<open>y = f x\<close> have "y \<in> f ` s" by simp
      then show "y \<in> f ` s \<union> v" by simp
    next
      assume "x \<in> f -` v"
      then have "f x \<in> v" by simp
      with \<open>y = f x\<close> have "y \<in> v" by simp
      then show "y \<in> f ` s \<union> v" by simp
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f ` (s \<union> f -` v) \<subseteq> f ` s \<union> v"
proof
  fix y
  assume "y \<in> f ` (s \<union> f -` v)"
  then show "y \<in> f ` s \<union> v"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s \<union> f -` v"
    then show "y \<in> f ` s \<union> v"
    proof
      assume "x \<in> s"
      then show "y \<in> f ` s \<union> v" by (simp add: \<open>y = f x\<close>)
    next
      assume "x \<in> f -` v"
      then show "y \<in> f ` s \<union> v" by (simp add: \<open>y = f x\<close>)
    qed
  qed
qed

(* 4\<ordfeminine> demostración *)

lemma "f ` (s \<union> f -` v) \<subseteq> f ` s \<union> v"
proof
  fix y
  assume "y \<in> f ` (s \<union> f -` v)"
  then show "y \<in> f ` s \<union> v"
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s \<union> f -` v"
    then show "y \<in> f ` s \<union> v" using \<open>y = f x\<close> by blast
  qed
qed

(* 5\<ordfeminine> demostración *)

lemma "f ` (s \<union> f -` u) \<subseteq> f ` s \<union> u"
  by auto

end
