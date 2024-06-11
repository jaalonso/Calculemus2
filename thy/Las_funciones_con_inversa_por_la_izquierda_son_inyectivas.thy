(* Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.thy
-- Las funciones con inversa por la izquierda son inyectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir que f tenga inversa por la
-- izquierda por
--    definition tiene_inversa_izq :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa_izq f \<longleftrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
-- Además, que f es inyectiva sobre un conjunto está definido por
--    definition inj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
--      where "inj_on f A \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y)"
-- y que f es inyectiva por
--    abbreviation inj :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
--       where "inj f \<equiv> inj_on f UNIV"
--
-- Demostrar que si f tiene inversa por la izquierda, entonces f es
-- inyectiva.
-- ------------------------------------------------------------------ *)

theory Las_funciones_con_inversa_por_la_izquierda_son_inyectivas
imports Main
begin

definition tiene_inversa_izq :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa_izq f \<longleftrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "tiene_inversa_izq f"
  shows   "inj f"
proof (unfold inj_def; intro allI impI)
  fix x y
  assume "f x = f y"
  obtain g where hg : "\<forall>x. g (f x) = x"
    using assms tiene_inversa_izq_def by auto
  have "x = g (f x)"
    by (simp only: hg)
  also have "\<dots> = g (f y)"
    by (simp only: \<open>f x = f y\<close>)
  also have "\<dots> = y"
    by (simp only: hg)
  finally show "x = y" .
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "tiene_inversa_izq f"
  shows   "inj f"
  by (metis assms inj_def tiene_inversa_izq_def)

end
