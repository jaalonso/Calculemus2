(* Imagen_inversa_de_la_union.thy
   f⁻¹[A \<union> B] = f⁻¹[A] \<union> f⁻¹[B].
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 5-abril-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f -` (u \<union> v) = f -` u \<union> f -` v
-- ------------------------------------------------------------------ *)

theory Imagen_inversa_de_la_union
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f -` (u \<union> v) = f -` u \<union> f -` v"
proof (rule equalityI)
  show "f -` (u \<union> v) \<subseteq> f -` u \<union> f -` v"
  proof (rule subsetI)
    fix x
    assume "x \<in> f -` (u \<union> v)"
    then have "f x \<in> u \<union> v"
      by (rule vimageD)
    then show "x \<in> f -` u \<union> f -` v"
    proof (rule UnE)
      assume "f x \<in> u"
      then have "x \<in> f -` u"
        by (rule vimageI2)
      then show "x \<in> f -` u \<union> f -` v"
        by (rule UnI1)
    next
      assume "f x \<in> v"
      then have "x \<in> f -` v"
        by (rule vimageI2)
      then show "x \<in> f -` u \<union> f -` v"
        by (rule UnI2)
    qed
  qed
next
  show "f -` u \<union> f -` v \<subseteq> f -` (u \<union> v)"
  proof (rule subsetI)
    fix x
    assume "x \<in> f -` u \<union> f -` v"
    then show "x \<in> f -` (u \<union> v)"
    proof (rule UnE)
      assume "x \<in> f -` u"
      then have "f x \<in> u"
        by (rule vimageD)
      then have "f x \<in> u \<union> v"
        by (rule UnI1)
      then show "x \<in> f -` (u \<union> v)"
        by (rule vimageI2)
    next
      assume "x \<in> f -` v"
      then have "f x \<in> v"
        by (rule vimageD)
      then have "f x \<in> u \<union> v"
        by (rule UnI2)
      then show "x \<in> f -` (u \<union> v)"
        by (rule vimageI2)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f -` (u \<union> v) = f -` u \<union> f -` v"
proof
  show "f -` (u \<union> v) \<subseteq> f -` u \<union> f -` v"
  proof
    fix x
    assume "x \<in> f -` (u \<union> v)"
    then have "f x \<in> u \<union> v" by simp
    then show "x \<in> f -` u \<union> f -` v"
    proof
      assume "f x \<in> u"
      then have "x \<in> f -` u" by simp
      then show "x \<in> f -` u \<union> f -` v" by simp
    next
      assume "f x \<in> v"
      then have "x \<in> f -` v" by simp
      then show "x \<in> f -` u \<union> f -` v" by simp
    qed
  qed
next
  show "f -` u \<union> f -` v \<subseteq> f -` (u \<union> v)"
  proof
    fix x
    assume "x \<in> f -` u \<union> f -` v"
    then show "x \<in> f -` (u \<union> v)"
    proof
      assume "x \<in> f -` u"
      then have "f x \<in> u" by simp
      then have "f x \<in> u \<union> v" by simp
      then show "x \<in> f -` (u \<union> v)" by simp
    next
      assume "x \<in> f -` v"
      then have "f x \<in> v" by simp
      then have "f x \<in> u \<union> v" by simp
      then show "x \<in> f -` (u \<union> v)" by simp
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f -` (u \<union> v) = f -` u \<union> f -` v"
  by (simp only: vimage_Un)

(* 4\<ordfeminine> demostración *)

lemma "f -` (u \<union> v) = f -` u \<union> f -` v"
  by auto

end
