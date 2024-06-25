(* La_equipotencia_es_una_relacion_de_equivalencia.thy
-- La equipotencia es una relación de equivalencia.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-junio-2024
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

theory La_equipotencia_es_una_relacion_de_equivalencia
imports Main "HOL-Library.Equipollence"
begin

(* 1\<ordfeminine> demostración *)

lemma "equivp (\<approx>)"
proof (rule equivpI)
  show "reflp (\<approx>)"
    using reflpI eqpoll_refl by blast
next
  show "symp (\<approx>)"
    using sympI eqpoll_sym by blast
next
  show "transp (\<approx>)"
    using transpI eqpoll_trans by blast
qed

(* 2\<ordfeminine> demostración *)

lemma "equivp (\<approx>)"
  by (simp add: equivp_reflp_symp_transp
                reflpI
                sympI
                eqpoll_sym
                transpI
                eqpoll_trans)

end
