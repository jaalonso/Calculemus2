(* Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.thy
-- Las funciones inyectivas tienen inversa por la izquierda.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-junio-2024
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
-- Demostrar que si f es una función inyectiva, entonces f tiene
-- inversa por la izquierda.
-- ------------------------------------------------------------------ *)

theory Las_funciones_inyectivas_tienen_inversa_por_la_izquierda
imports Main
begin

definition tiene_inversa_izq :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa_izq f \<longleftrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows   "tiene_inversa_izq f"
proof (unfold tiene_inversa_izq_def)
  let ?g = "(\<lambda>y. SOME x. f x = y)"
  have "\<forall>x. ?g (f x) = x"
  proof (rule allI)
    fix a
    have "\<exists>x. f x = f a"
      by auto
    then have "f (?g (f a)) = f a"
      by (rule someI_ex)
    then show "?g (f a) = a"
      using assms
      by (simp only: injD)
  qed
  then show "(\<exists>g. \<forall>x. g (f x) = x)"
    by (simp only: exI)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows   "tiene_inversa_izq f"
proof (unfold tiene_inversa_izq_def)
  have "\<forall>x. inv f (f x) = x"
  proof (rule allI)
    fix x
    show "inv f (f x) = x"
      using assms by (simp only: inv_f_f)
  qed
  then show "(\<exists>g. \<forall>x. g (f x) = x)"
    by (simp only: exI)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "inj f"
  shows   "tiene_inversa_izq f"
proof (unfold tiene_inversa_izq_def)
  have "\<forall>x. inv f (f x) = x"
    by (simp add: assms)
  then show "(\<exists>g. \<forall>x. g (f x) = x)"
    by (simp only: exI)
qed

end
