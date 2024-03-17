(* Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.thy
-- Si f es inyectiva, entonces f⁻¹[f[s]] ⊆ s
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-marzo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si f es inyectiva, entonces
--    f⁻¹[f[s]] ⊆ s
-- ------------------------------------------------------------------- *)

theory Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
proof (rule subsetI)
  fix x
  assume "x ∈ f -` (f ` s)"
  then have "f x ∈ f ` s"
    by (rule vimageD)
  then show "x ∈ s"
  proof (rule imageE)
    fix y
    assume "f x = f y"
    assume "y ∈ s"
    have "x = y"
      using ‹inj f› ‹f x = f y› by (rule injD)
    then show "x ∈ s"
      using ‹y ∈ s›  by (rule ssubst)
  qed
qed

(* 2ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
proof
  fix x
  assume "x ∈ f -` (f ` s)"
  then have "f x ∈ f ` s"
    by simp
  then show "x ∈ s"
  proof
    fix y
    assume "f x = f y"
    assume "y ∈ s"
    have "x = y"
      using ‹inj f› ‹f x = f y› by (rule injD)
    then show "x ∈ s"
      using ‹y ∈ s›  by simp
  qed
qed

(* 3ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
  using assms
  unfolding inj_def
  by auto

(* 4ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
  using assms
  by (simp only: inj_vimage_image_eq)

end
