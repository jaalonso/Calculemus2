(*
 If_x_is_the_supremum_of_set_A_then_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a.thy
-- If x is the supremum of set A, then ((\<forall> y)[y < x \<rightarrow> (\<exists> a \<in> A)[y < a]]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, August 31, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL, one can define that x is an upper bound of A by
--    definition is_upper_bound :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
--      "is_upper_bound A x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
-- and x is supremum of A by
--    definition is_supremum :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
--      "is_supremum A x \<longleftrightarrow> (is_upper_bound A x \<and>
--                           (\<forall> y. is_upper_bound A y \<longrightarrow> x \<le> y))"
--
-- Prove that if x is the supremum of A, then
--    "\<forall>y<x. \<exists>a\<in>A. y < a"
-- ------------------------------------------------------------------ *)

theory "If_x_is_the_supremum_of_set_A_then_forall_y_y_lt_x_to_exists_a_in_A_y_lt_a"
  imports Main HOL.Real
begin

definition is_upper_bound :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
  "is_upper_bound A x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"

definition is_supremum :: "(real set) \<Rightarrow> real \<Rightarrow> bool" where
  "is_supremum A x \<longleftrightarrow> (is_upper_bound A x \<and>
                       (\<forall> y. is_upper_bound A y \<longrightarrow> x \<le> y))"

(* Proof 1 *)
lemma
  assumes "is_supremum A x"
  shows   "\<forall>y<x. \<exists>a\<in>A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "\<exists>a\<in>A. y < a"
  proof (rule ccontr)
    assume "\<not> (\<exists>a\<in>A. y < a)"
    then have "\<forall>a\<in>A. a \<le> y"
      by auto
    then have "is_upper_bound A y"
      using is_upper_bound_def by simp
    then have "x \<le> y"
      using assms is_supremum_def by simp
    then have "x < x"
      using \<open>y < x\<close> by simp
    then show False by simp
  qed
qed

(* Proof 2 *)
lemma
  assumes "is_supremum A x"
  shows   "\<forall>y<x. \<exists>a\<in>A. y < a"
proof (intro allI impI)
  fix y
  assume "y < x"
  show "\<exists>a\<in>A. y < a"
  proof (rule ccontr)
    assume "\<not> (\<exists>a\<in>A. y < a)"
    then have "is_upper_bound A y"
      using is_upper_bound_def by auto
    then show "False"
      using assms is_supremum_def \<open>y < x\<close> by auto
  qed
qed

end
