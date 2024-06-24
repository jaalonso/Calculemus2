(* La_equipotencia_es_una_relacion_transitiva.lean
-- La equipotencia es una relación transitiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Dos conjuntos A y B son equipotentes (y se denota por A \<simeq> B) si
-- existe una aplicación biyectiva entre ellos. La equipotencia está
-- definida en Isabelle por
--    definition eqpoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl "\<approx>" 50)
--      where "eqpoll A B \<equiv> \<exists>f. bij_betw f A B"
--
-- Demostrar que la relación de equipotencia es transitiva.
-- ------------------------------------------------------------------ *)

theory La_equipotencia_es_una_relacion_transitiva
imports Main "HOL-Library.Equipollence"
begin

(* 1\<ordfeminine> demostración *)

lemma "transp (\<approx>)"
proof (rule transpI)
  fix x y z :: "'a set"
  assume "x \<approx> y" and "y \<approx> z"
  show "x \<approx> z"
  proof (unfold eqpoll_def)
    obtain f where hf : "bij_betw f x y"
      using \<open>x \<approx> y\<close> eqpoll_def by auto
    obtain g where hg : "bij_betw g y z"
      using \<open>y \<approx> z\<close> eqpoll_def by auto
    have "bij_betw (g \<circ> f) x z"
      using hf hg by (rule bij_betw_trans)
    then show "\<exists>h. bij_betw h x z"
      by auto
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "transp (\<approx>)"
  unfolding eqpoll_def transp_def
  by (meson bij_betw_trans)

(* 3\<ordfeminine> demostración *)

lemma "transp (\<approx>)"
  by (simp add: eqpoll_trans transpI)

end
