(* Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.thy
-- Las funciones suprayectivas tienen inversa por la derecha.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-junio-2024
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

theory Las_funciones_suprayectivas_tienen_inversa_por_la_derecha
imports Main
begin

definition tiene_inversa_dcha :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa_dcha f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  let ?g = "\<lambda>y. SOME x. f x = y"
  have "\<forall>y. f (?g y) = y"
  proof (rule allI)
    fix y
    have "\<exists>x. y = f x"
      using assms by (rule surjD)
    then have "\<exists>x. f x = y"
      by auto
    then show "f (?g y) = y"
      by (rule someI_ex)
  qed
  then show "\<exists>g. \<forall>y. f (g y) = y"
    by auto
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  let ?g = "\<lambda>y. SOME x. f x = y"
  have "\<forall>y. f (?g y) = y"
  proof (rule allI)
    fix y
    have "\<exists>x. f x = y"
      by (metis assms surjD)
    then show "f (?g y) = y"
      by (rule someI_ex)
  qed
  then show "\<exists>g. \<forall>y. f (g y) = y"
    by auto
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  have "\<forall>y. f (inv f y) = y"
    by (simp add: assms surj_f_inv_f)
  then show "\<exists>g. \<forall>y. f (g y) = y"
    by auto
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
  by (metis assms surjD tiene_inversa_dcha_def)

end
