(* La_equipotencia_es_una_relacion_reflexiva.thy
-- La equipotencia es una relación reflexiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Dos conjuntos A y B son equipotentes (y se denota por A \<simeq> B) si
-- existe una aplicación biyectiva entre ellos. La equipotencia está
-- definida en Isabelle por
--    definition eqpoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl "\<approx>" 50)
--      where "eqpoll A B \<equiv> \<exists>f. bij_betw f A B"
--
-- Demostrar que la relación de equipotencia es reflexiva.
-- ------------------------------------------------------------------ *)

theory La_equipotencia_es_una_relacion_reflexiva
imports Main "HOL-Library.Equipollence"
begin

(* 1\<ordfeminine> demostración *)

lemma "reflp (\<approx>)"
proof (rule reflpI)
  fix x :: "'a set"
  have "bij_betw id x x"
    by (simp only: bij_betw_id)
  then have "\<exists>f. bij_betw f x x"
    by (simp only: exI)
  then show "x \<approx> x"
    by (simp only: eqpoll_def)
qed

(* 2\<ordfeminine> demostración *)

lemma "reflp (\<approx>)"
by (simp only: reflpI eqpoll_refl)

(* 3\<ordfeminine> demostración *)

lemma "reflp (\<approx>)"
by (simp add: reflpI)

end
