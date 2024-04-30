(* Imagen_inversa_de_la_union_general.thy
-- Imagen inversa de la unión general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f⁻¹[\<Union>ᵢ Bᵢ] = \<Union>ᵢ f⁻¹[Bᵢ]
-- ------------------------------------------------------------------ *)

theory Imagen_inversa_de_la_union_general
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f -` (\<Union> i \<in> I. B i) = (\<Union> i \<in> I. f -` B i)"
proof (rule equalityI)
  show "f -` (\<Union> i \<in> I. B i) \<subseteq> (\<Union> i \<in> I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume "x \<in> f -` (\<Union> i \<in> I. B i)"
    then have "f x \<in> (\<Union> i \<in> I. B i)"
      by (rule vimageD)
    then show "x \<in> (\<Union> i \<in> I. f -` B i)"
    proof (rule UN_E)
      fix i
      assume "i \<in> I"
      assume "f x \<in> B i"
      then have "x \<in> f -` B i"
        by (rule vimageI2)
      with \<open>i \<in> I\<close> show "x \<in> (\<Union> i \<in> I. f -` B i)"
        by (rule UN_I)
    qed
  qed
next
  show "(\<Union> i \<in> I. f -` B i) \<subseteq> f -` (\<Union> i \<in> I. B i)"
  proof (rule subsetI)
    fix x
    assume "x \<in> (\<Union> i \<in> I. f -` B i)"
    then show "x \<in> f -` (\<Union> i \<in> I. B i)"
    proof (rule UN_E)
      fix i
      assume "i \<in> I"
      assume "x \<in> f -` B i"
      then have "f x \<in> B i"
        by (rule vimageD)
      with \<open>i \<in> I\<close> have "f x \<in> (\<Union> i \<in> I. B i)"
        by (rule UN_I)
      then show "x \<in> f -` (\<Union> i \<in> I. B i)"
        by (rule vimageI2)
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f -` (\<Union> i \<in> I. B i) = (\<Union> i \<in> I. f -` B i)"
proof
  show "f -` (\<Union> i \<in> I. B i) \<subseteq> (\<Union> i \<in> I. f -` B i)"
  proof
    fix x
    assume "x \<in> f -` (\<Union> i \<in> I. B i)"
    then have "f x \<in> (\<Union> i \<in> I. B i)" by simp
    then show "x \<in> (\<Union> i \<in> I. f -` B i)"
    proof
      fix i
      assume "i \<in> I"
      assume "f x \<in> B i"
      then have "x \<in> f -` B i" by simp
      with \<open>i \<in> I\<close> show "x \<in> (\<Union> i \<in> I. f -` B i)" by (rule UN_I)
    qed
  qed
next
  show "(\<Union> i \<in> I. f -` B i) \<subseteq> f -` (\<Union> i \<in> I. B i)"
  proof
    fix x
    assume "x \<in> (\<Union> i \<in> I. f -` B i)"
    then show "x \<in> f -` (\<Union> i \<in> I. B i)"
    proof
      fix i
      assume "i \<in> I"
      assume "x \<in> f -` B i"
      then have "f x \<in> B i" by simp
      with \<open>i \<in> I\<close> have "f x \<in> (\<Union> i \<in> I. B i)" by (rule UN_I)
      then show "x \<in> f -` (\<Union> i \<in> I. B i)" by simp
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f -` (\<Union> i \<in> I. B i) = (\<Union> i \<in> I. f -` B i)"
  by (simp only: vimage_UN)

(* 4\<ordfeminine> demostración *)

lemma "f -` (\<Union> i \<in> I. B i) = (\<Union> i \<in> I. f -` B i)"
  by auto

end
