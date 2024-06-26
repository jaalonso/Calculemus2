(* La_igualdad_de_valores_es_una_relacion_de_equivalencia.thy
-- La igualdad de valores es una relación de equivalencia.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean X e Y dos conjuntos y f una función de X en Y. Se define la
-- relación R en X de forma que x está relacionado con y si f(x) = f(y).
--
-- Demostrar que R es una relación de equivalencia.
-- ------------------------------------------------------------------ *)

theory La_igualdad_de_valores_es_una_relacion_de_equivalencia
imports Main
begin

definition R :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "R f x y \<longleftrightarrow> (f x = f y)"

(* 1\<ordfeminine> demostración *)

lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
  proof (rule reflpI)
    fix x
    have "f x = f x"
      by (rule refl)
    then show "R f x x"
      by (unfold R_def)
  qed
next
  show "symp (R f)"
  proof (rule sympI)
    fix x y
    assume "R f x y"
    then have "f x = f y"
      by (unfold R_def)
    then have "f y = f x"
      by (rule sym)
    then show "R f y x"
      by (unfold R_def)
  qed
next
  show "transp (R f)"
  proof (rule transpI)
    fix x y z
    assume "R f x y" and "R f y z"
    then have "f x = f y" and "f y = f z"
      by (unfold R_def)
    then have "f x = f z"
      by (rule ssubst)
    then show "R f x z"
      by (unfold R_def)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
  proof (rule reflpI)
    fix x
    show "R f x x"
      by (metis R_def)
  qed
next
  show "symp (R f)"
  proof (rule sympI)
    fix x y
    assume "R f x y"
    then show "R f y x"
      by (metis R_def)
  qed
next
  show "transp (R f)"
  proof (rule transpI)
    fix x y z
    assume "R f x y" and "R f y z"
    then show "R f x z"
      by (metis R_def)
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
    by (simp add: R_def reflpI)
next
  show "symp (R f)"
    by (metis R_def sympI)
next
  show "transp (R f)"
    by (metis R_def transpI)
qed

(* 4\<ordfeminine> demostración *)

lemma "equivp (R f)"
  by (metis R_def
            equivpI
            reflpI
            sympI
            transpI)

end
