(* La_equipotencia_es_una_relacion_simetrica.thy
-- La equipotencia es una relación simétrica.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Dos conjuntos A y B son equipotentes (y se denota por A \<simeq> B) si
-- existe una aplicación biyectiva entre ellos. La equipotencia está
-- definida en Isabelle por
--    definition eqpoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl "\<approx>" 50)
--      where "eqpoll A B \<equiv> \<exists>f. bij_betw f A B"
--
-- Demostrar que la relación de equipotencia es simétrica.
-- ------------------------------------------------------------------ *)

theory La_equipotencia_es_una_relacion_simetrica
imports Main "HOL-Library.Equipollence"
begin

(* 1\<ordfeminine> demostración *)

lemma "symp (\<approx>)"
proof (rule sympI)
  fix x y :: "'a set"
  assume "x \<approx> y"
  then obtain f where "bij_betw f x y"
    using eqpoll_def by blast
  then have "bij_betw (the_inv_into x f) y x"
    by (rule bij_betw_the_inv_into)
  then have "\<exists>g. bij_betw g y x"
    by auto
  then show "y \<approx> x"
    by (simp only: eqpoll_def)
qed

(* 2\<ordfeminine> demostración *)

lemma "symp (\<approx>)"
  unfolding eqpoll_def symp_def
  using bij_betw_the_inv_into by auto

(* 3\<ordfeminine> demostración *)

lemma "symp (\<approx>)"
  by (simp add: eqpoll_sym sympI)

end
