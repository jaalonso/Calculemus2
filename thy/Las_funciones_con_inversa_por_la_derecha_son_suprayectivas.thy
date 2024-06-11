(* Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.thy
-- Las funciones con inversa por la derecha son suprayectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir que f tenga inversa por la
-- derecha por
--    definition tiene_inversa_dcha :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa_dcha f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"
--
-- Demostrar que si f es una función suprayectiva, entonces f tiene
-- inversa por la derecha.
-- ------------------------------------------------------------------ *)

theory Las_funciones_con_inversa_por_la_derecha_son_suprayectivas
imports Main
begin

definition tiene_inversa_dcha :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa_dcha f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "\<forall>y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then have "f (g y) = y"
    by (rule allE)
  then have "y = f (g y)"
    by (rule sym)
  then show "\<exists>x. y = f x"
    by (rule exI)
qed

(* 2\<ordfeminine> demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "\<forall>y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then have "y = f (g y)"
    by simp
  then show "\<exists>x. y = f x"
    by (rule exI)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "\<forall>y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then show "\<exists>x. y = f x"
    by metis
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  show "\<exists>x. y = f x"
    using assms tiene_inversa_dcha_def
    by metis
qed

(* 5\<ordfeminine> demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
using assms tiene_inversa_dcha_def surj_def
by metis

end
