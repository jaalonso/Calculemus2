(* Imagen_de_la_interseccion_general.thy
-- Imagen de la intersección general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-abril-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f[\<Inter>ᵢ Aᵢ] \<subseteq> \<Inter>ᵢ f[Aᵢ]
-- ------------------------------------------------------------------ *)

theory Imagen_de_la_interseccion_general
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f ` (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. f ` A i)"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` (\<Inter> i \<in> I. A i)"
  then show "y \<in> (\<Inter> i \<in> I. f ` A i)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume xIA : "x \<in> (\<Inter> i \<in> I. A i)"
    have "f x \<in> (\<Inter> i \<in> I. f ` A i)"
    proof (rule INT_I)
      fix i
      assume "i \<in> I"
      with xIA have "x \<in> A i"
        by (rule INT_D)
      then show "f x \<in> f ` A i"
        by (rule imageI)
    qed
    with \<open>y = f x\<close> show "y \<in> (\<Inter> i \<in> I. f ` A i)"
      by (rule ssubst)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "f ` (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. f ` A i)"
proof
  fix y
  assume "y \<in> f ` (\<Inter> i \<in> I. A i)"
  then show "y \<in> (\<Inter> i \<in> I. f ` A i)"
  proof
    fix x
    assume "y = f x"
    assume xIA : "x \<in> (\<Inter> i \<in> I. A i)"
    have "f x \<in> (\<Inter> i \<in> I. f ` A i)"
    proof
      fix i
      assume "i \<in> I"
      with xIA have "x \<in> A i" by simp
      then show "f x \<in> f ` A i" by simp
    qed
    with \<open>y = f x\<close> show "y \<in> (\<Inter> i \<in> I. f ` A i)" by simp
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "f ` (\<Inter> i \<in> I. A i) \<subseteq> (\<Inter> i \<in> I. f ` A i)"
  by blast

end
