(* Imagen_inversa_de_la_interseccion.thy
   f⁻¹[u \<inter> v] = f⁻¹[u] \<inter> f⁻¹[v]
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 12-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
  En Isabelle/HOL, la imagen inversa de un conjunto s (de elementos de
  tipo \<beta>) por la función f (de tipo \<alpha> \<rightarrow> \<beta>) es el conjunto `f -` s` de
  elementos x (de tipo \<alpha>) tales que `f x \<in> s`.

   Demostrar que
      f ⁻¹' (u \<inter> v) = f ⁻¹' u \<inter> f ⁻¹' v
  ------------------------------------------------------------------- *)

theory Imagen_inversa_de_la_interseccion
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "f -` (u \<inter> v) = f -` u \<inter> f -` v"
proof (rule equalityI)
  show "f -` (u \<inter> v) \<subseteq> f -` u \<inter> f -` v"
  proof (rule subsetI)
    fix x
    assume "x \<in> f -` (u \<inter> v)"
    then have h : "f x \<in> u \<inter> v"
      by (simp only: vimage_eq)
    have "x \<in> f -` u"
    proof -
      have "f x \<in> u"
        using h by (rule IntD1)
      then show "x \<in> f -` u"
        by (rule vimageI2)
    qed
    moreover
    have "x \<in> f -` v"
    proof -
      have "f x \<in> v"
        using h by (rule IntD2)
      then show "x \<in> f -` v"
        by (rule vimageI2)
    qed
    ultimately show "x \<in> f -` u \<inter> f -` v"
      by (rule IntI)
  qed
next
  show "f -` u \<inter> f -` v \<subseteq> f -` (u \<inter> v)"
  proof (rule subsetI)
    fix x
    assume h2 : "x \<in> f -` u \<inter> f -` v"
    have "f x \<in> u"
    proof -
      have "x \<in> f -` u"
        using h2 by (rule IntD1)
      then show "f x \<in> u"
        by (rule vimageD)
    qed
    moreover
    have "f x \<in> v"
    proof -
      have "x \<in> f -` v"
        using h2 by (rule IntD2)
      then show "f x \<in> v"
        by (rule vimageD)
    qed
    ultimately have "f x \<in> u \<inter> v"
      by (rule IntI)
    then show "x \<in> f -` (u \<inter> v)"
      by (rule vimageI2)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "f -` (u \<inter> v) = f -` u \<inter> f -` v"
proof
  show "f -` (u \<inter> v) \<subseteq> f -` u \<inter> f -` v"
  proof
    fix x
    assume "x \<in> f -` (u \<inter> v)"
    then have h : "f x \<in> u \<inter> v"
      by simp
    have "x \<in> f -` u"
    proof -
      have "f x \<in> u"
        using h by simp
      then show "x \<in> f -` u"
        by simp
    qed
    moreover
    have "x \<in> f -` v"
    proof -
      have "f x \<in> v"
        using h by simp
      then show "x \<in> f -` v"
        by simp
    qed
    ultimately show "x \<in> f -` u \<inter> f -` v"
      by simp
  qed
next
  show "f -` u \<inter> f -` v \<subseteq> f -` (u \<inter> v)"
  proof
    fix x
    assume h2 : "x \<in> f -` u \<inter> f -` v"
    have "f x \<in> u"
    proof -
      have "x \<in> f -` u"
        using h2 by simp
      then show "f x \<in> u"
        by simp
    qed
    moreover
    have "f x \<in> v"
    proof -
      have "x \<in> f -` v"
        using h2 by simp
      then show "f x \<in> v"
        by simp
    qed
    ultimately have "f x \<in> u \<inter> v"
      by simp
    then show "x \<in> f -` (u \<inter> v)"
      by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "f -` (u \<inter> v) = f -` u \<inter> f -` v"
proof
  show "f -` (u \<inter> v) \<subseteq> f -` u \<inter> f -` v"
  proof
    fix x
    assume h1 : "x \<in> f -` (u \<inter> v)"
    have "x \<in> f -` u" using h1 by simp
    moreover
    have "x \<in> f -` v" using h1 by simp
    ultimately show "x \<in> f -` u \<inter> f -` v" by simp
  qed
next
  show "f -` u \<inter> f -` v \<subseteq> f -` (u \<inter> v)"
  proof
    fix x
    assume h2 : "x \<in> f -` u \<inter> f -` v"
    have "f x \<in> u" using h2 by simp
    moreover
    have "f x \<in> v" using h2 by simp
    ultimately have "f x \<in> u \<inter> v" by simp
    then show "x \<in> f -` (u \<inter> v)" by simp
  qed
qed

(* 4\<ordfeminine> demostración *)
lemma "f -` (u \<inter> v) = f -` u \<inter> f -` v"
  by (simp only: vimage_Int)

(* 5\<ordfeminine> demostración *)
lemma "f -` (u \<inter> v) = f -` u \<inter> f -` v"
  by auto

end
