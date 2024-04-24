(* Union_con_la_imagen_inversa.thy
-- Unión con la imagen inversa
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    s \<union> f⁻¹[v] \<subseteq> f⁻¹[f[s] \<union> v]
-- ------------------------------------------------------------------ *)

theory Union_con_la_imagen_inversa
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "s \<union> f -` v \<subseteq> f -` (f ` s \<union> v)"
proof (rule subsetI)
  fix x
  assume "x \<in> s \<union> f -` v"
  then have "f x \<in> f ` s \<union> v"
  proof (rule UnE)
    assume "x \<in> s"
    then have "f x \<in> f ` s"
      by (rule imageI)
    then show "f x \<in> f ` s \<union> v"
      by (rule UnI1)
  next
    assume "x \<in> f -` v"
    then have "f x \<in> v"
      by (rule vimageD)
    then show "f x \<in> f ` s \<union> v"
      by (rule UnI2)
  qed
  then show "x \<in> f -` (f ` s \<union> v)"
    by (rule vimageI2)
qed

(* 2\<ordfeminine> demostración *)

lemma "s \<union> f -` v \<subseteq> f -` (f ` s \<union> v)"
proof
  fix x
  assume "x \<in> s \<union> f -` v"
  then have "f x \<in> f ` s \<union> v"
  proof
    assume "x \<in> s"
    then have "f x \<in> f ` s" by simp
    then show "f x \<in> f ` s \<union> v" by simp
  next
    assume "x \<in> f -` v"
    then have "f x \<in> v" by simp
    then show "f x \<in> f ` s \<union> v" by simp
  qed
  then show "x \<in> f -` (f ` s \<union> v)" by simp
qed

(* 3\<ordfeminine> demostración *)

lemma "s \<union> f -` v \<subseteq> f -` (f ` s \<union> v)"
proof
  fix x
  assume "x \<in> s \<union> f -` v"
  then have "f x \<in> f ` s \<union> v"
  proof
    assume "x \<in> s"
    then show "f x \<in> f ` s \<union> v" by simp
  next
    assume "x \<in> f -` v"
    then show "f x \<in> f ` s \<union> v" by simp
  qed
  then show "x \<in> f -` (f ` s \<union> v)" by simp
qed

(* 4\<ordfeminine> demostración *)

lemma "s \<union> f -` v \<subseteq> f -` (f ` s \<union> v)"
  by auto

end
