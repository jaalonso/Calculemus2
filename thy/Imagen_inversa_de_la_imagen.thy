(* Imagen_inversa_de_la_imagen.thy
   s \<subseteq> f⁻¹[f[s]]
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 14-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Demostrar que si s es un subconjunto del dominio de la función f,
   entonces s está contenido en la imagen inversa de la imagen de s por
   f; es decir,
      s \<subseteq> f⁻¹[f[s]]
  ------------------------------------------------------------------- *)

theory Imagen_inversa_de_la_imagen
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s \<subseteq> f -` (f ` s)"
proof (rule subsetI)
  fix x
  assume "x \<in> s"
  then have "f x \<in> f ` s"
    by (simp only: imageI)
  then show "x \<in> f -` (f ` s)"
    by (simp only: vimageI)
qed

(* 2\<ordfeminine> demostración *)
lemma "s \<subseteq> f -` (f ` s)"
proof
  fix x
  assume "x \<in> s"
  then have "f x \<in> f ` s" by simp
  then show "x \<in> f -` (f ` s)" by simp
qed

(* 3\<ordfeminine> demostración *)
lemma "s \<subseteq> f -` (f ` s)"
  by auto

end
