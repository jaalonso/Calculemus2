(* Imagen_inversa_de_la_interseccion_general.thy
-- Imagen inversa de la intersección general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f⁻¹[\<Inter>ᵢ B i] = \<Inter>ᵢ f⁻¹[Bᵢ]
-- ------------------------------------------------------------------ *)

theory Imagen_inversa_de_la_interseccion_general
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f -` (\<Inter> i \<in> I. B i) = (\<Inter> i \<in> I. f -` B i)"
proof (rule equalityI)
  show "f -` (\<Inter> i \<in> I. B i) \<subseteq> (\<Inter> i \<in> I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume "x \<in> f -` (\<Inter> i \<in> I. B i)"
    show "x \<in> (\<Inter> i \<in> I. f -` B i)"
    proof (rule INT_I)
      fix i
      assume "i \<in> I"
      have "f x \<in> (\<Inter> i \<in> I. B i)"
        using \<open>x \<in> f -` (\<Inter> i \<in> I. B i)\<close> by (rule vimageD)
      then have "f x \<in> B i"
        using \<open>i \<in> I\<close> by (rule INT_D)
      then show "x \<in> f -` B i"
        by (rule vimageI2)
    qed
  qed
next
  show "(\<Inter> i \<in> I. f -` B i) \<subseteq> f -` (\<Inter> i \<in> I. B i)"
  proof (rule subsetI)
    fix x
    assume "x \<in> (\<Inter> i \<in> I. f -` B i)"
    have "f x \<in> (\<Inter> i \<in> I. B i)"
    proof (rule INT_I)
      fix i
      assume "i \<in> I"
      with \<open>x \<in> (\<Inter> i \<in> I. f -` B i)\<close> have "x \<in> f -` B i"
        by (rule INT_D)
      then show "f x \<in> B i"
        by (rule vimageD)
    qed
    then show "x \<in> f -` (\<Inter> i \<in> I. B i)"
      by (rule vimageI2)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f -` (\<Inter> i \<in> I. B i) = (\<Inter> i \<in> I. f -` B i)"
proof
  show "f -` (\<Inter> i \<in> I. B i) \<subseteq> (\<Inter> i \<in> I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume hx : "x \<in> f -` (\<Inter> i \<in> I. B i)"
    show "x \<in> (\<Inter> i \<in> I. f -` B i)"
    proof
      fix i
      assume "i \<in> I"
      have "f x \<in> (\<Inter> i \<in> I. B i)" using hx by simp
      then have "f x \<in> B i" using \<open>i \<in> I\<close> by simp
      then show "x \<in> f -` B i" by simp
    qed
  qed
next
  show "(\<Inter> i \<in> I. f -` B i) \<subseteq> f -` (\<Inter> i \<in> I. B i)"
  proof
    fix x
    assume "x \<in> (\<Inter> i \<in> I. f -` B i)"
    have "f x \<in> (\<Inter> i \<in> I. B i)"
    proof
      fix i
      assume "i \<in> I"
      with \<open>x \<in> (\<Inter> i \<in> I. f -` B i)\<close> have "x \<in> f -` B i" by simp
      then show "f x \<in> B i" by simp
    qed
    then show "x \<in> f -` (\<Inter> i \<in> I. B i)" by simp
  qed
qed

(* 3 demostración *)

lemma "f -` (\<Inter> i \<in> I. B i) = (\<Inter> i \<in> I. f -` B i)"
  by (simp only: vimage_INT)

(* 4\<ordfeminine> demostración *)

lemma "f -` (\<Inter> i \<in> I. B i) = (\<Inter> i \<in> I. f -` B i)"
  by auto

end
