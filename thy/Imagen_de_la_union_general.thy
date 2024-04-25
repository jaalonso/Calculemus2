(* Imagen_de_la_union_general.thy
-- Imagen de la unión general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f[\<Union>ᵢAᵢ] = \<Union>ᵢf[Aᵢ]
-- ------------------------------------------------------------------ *)

theory Imagen_de_la_union_general
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f ` (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. f ` A i)"
proof (rule equalityI)
  show "f ` (\<Union> i \<in> I. A i) \<subseteq> (\<Union> i \<in> I. f ` A i)"
  proof (rule subsetI)
    fix y
    assume "y \<in> f ` (\<Union> i \<in> I. A i)"
    then show "y \<in> (\<Union> i \<in> I. f ` A i)"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x \<in> (\<Union> i \<in> I. A i)"
      then have "f x \<in> (\<Union> i \<in> I. f ` A i)"
      proof (rule UN_E)
        fix i
        assume "i \<in> I"
        assume "x \<in> A i"
        then have "f x \<in> f ` A i"
          by (rule imageI)
        with \<open>i \<in> I\<close> show "f x \<in> (\<Union> i \<in> I. f ` A i)"
          by (rule UN_I)
      qed
      with \<open>y = f x\<close> show "y \<in> (\<Union> i \<in> I. f ` A i)"
        by (rule ssubst)
    qed
  qed
next
  show "(\<Union> i \<in> I. f ` A i) \<subseteq> f ` (\<Union> i \<in> I. A i)"
  proof (rule subsetI)
    fix y
    assume "y \<in> (\<Union> i \<in> I. f ` A i)"
    then show "y \<in> f ` (\<Union> i \<in> I. A i)"
    proof (rule UN_E)
      fix i
      assume "i \<in> I"
      assume "y \<in> f ` A i"
      then show "y \<in> f ` (\<Union> i \<in> I. A i)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x \<in> A i"
        with \<open>i \<in> I\<close> have "x \<in> (\<Union> i \<in> I. A i)"
          by (rule UN_I)
        then have "f x \<in> f ` (\<Union> i \<in> I. A i)"
          by (rule imageI)
        with \<open>y = f x\<close> show "y \<in> f ` (\<Union> i \<in> I. A i)"
          by (rule ssubst)
      qed
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f ` (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. f ` A i)"
proof
  show "f ` (\<Union> i \<in> I. A i) \<subseteq> (\<Union> i \<in> I. f ` A i)"
  proof
    fix y
    assume "y \<in> f ` (\<Union> i \<in> I. A i)"
    then show "y \<in> (\<Union> i \<in> I. f ` A i)"
    proof
      fix x
      assume "y = f x"
      assume "x \<in> (\<Union> i \<in> I. A i)"
      then have "f x \<in> (\<Union> i \<in> I. f ` A i)"
      proof
        fix i
        assume "i \<in> I"
        assume "x \<in> A i"
        then have "f x \<in> f ` A i" by simp
        with \<open>i \<in> I\<close> show "f x \<in> (\<Union> i \<in> I. f ` A i)" by (rule UN_I)
      qed
      with \<open>y = f x\<close> show "y \<in> (\<Union> i \<in> I. f ` A i)" by simp
    qed
  qed
next
  show "(\<Union> i \<in> I. f ` A i) \<subseteq> f ` (\<Union> i \<in> I. A i)"
  proof
    fix y
    assume "y \<in> (\<Union> i \<in> I. f ` A i)"
    then show "y \<in> f ` (\<Union> i \<in> I. A i)"
    proof
      fix i
      assume "i \<in> I"
      assume "y \<in> f ` A i"
      then show "y \<in> f ` (\<Union> i \<in> I. A i)"
      proof
        fix x
        assume "y = f x"
        assume "x \<in> A i"
        with \<open>i \<in> I\<close> have "x \<in> (\<Union> i \<in> I. A i)" by (rule UN_I)
        then have "f x \<in> f ` (\<Union> i \<in> I. A i)" by simp
        with \<open>y = f x\<close> show "y \<in> f ` (\<Union> i \<in> I. A i)" by simp
      qed
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f ` (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. f ` A i)"
  by (simp only: image_UN)

(* 4\<ordfeminine> demostración *)

lemma "f ` (\<Union> i \<in> I. A i) = (\<Union> i \<in> I. f ` A i)"
  by auto

end
