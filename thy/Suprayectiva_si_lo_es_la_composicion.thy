(* Suprayectiva_si_lo_es_la_composicion.thy
-- Si g \<circ> f es suprayectiva, entonces f es suprayectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean f: X \<rightarrow> Y y g: Y \<rightarrow> Z. Demostrar que si g \<circ> f es suprayectiva,
-- entonces g es suprayectiva.
-- ------------------------------------------------------------------- *)

theory Suprayectiva_si_lo_es_la_composicion
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "surj (g \<circ> f)"
  shows "surj g"
proof (unfold Fun.surj_def, rule)
  fix z
  have "\<exists>x. z = (g \<circ> f) x"
    using assms 
    by (rule surjD)
  then obtain x where "z = (g \<circ> f) x"
    by (rule exE)
  then have "z = g (f x)"
    by (simp only: Fun.comp_apply)
  then show "\<exists>y. z = g y"
    by (rule exI)
qed

(* 2 demostración *)

lemma
  assumes "surj (g \<circ> f)"
  shows "surj g"
using assms
by auto

end
