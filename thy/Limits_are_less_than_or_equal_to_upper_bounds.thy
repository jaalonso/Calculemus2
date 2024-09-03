(* Limits_are_less_than_or_equal_to_upper_bounds.lean
-- If x is the limit of u and y is an upper bound of u, then x \<le> y.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 3, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL, we can define that a is the limit of the sequence u
-- by:
--    definition is_limit :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "is_limit u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
-- and that a is an upper bound of u by:
--    definition is_upper_bound :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "is_upper_bound u c \<longleftrightarrow> (\<forall>n. u n \<le> c)"
--
-- Prove that if x is the limit of the sequence u and y is an upper
-- bound of u, then x \<le> y.
-- ------------------------------------------------------------------ *)

theory Limits_are_less_than_or_equal_to_upper_bounds
imports Main HOL.Real
begin

definition is_limit :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "is_limit u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

definition is_upper_bound :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "is_upper_bound u c \<longleftrightarrow> (\<forall>n. u n \<le> c)"

(* Proof 1 *)
lemma
  fixes x y :: real
  assumes "is_limit u x"
          "is_upper_bound u y"
  shows   "x \<le> y"
proof (rule field_le_epsilon)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - x\<bar> < \<epsilon>"
    using assms(1) is_limit_def by auto
  then have "\<bar>u k - x\<bar> < \<epsilon>"
    by simp
  then have "-\<epsilon> < u k - x"
    by simp
  then have "x < u k + \<epsilon>"
    by simp
  moreover have "u k \<le> y"
    using assms(2) is_upper_bound_def by simp
  ultimately show "x \<le> y + \<epsilon>"
    by simp
qed

(* Proof 2 *)
lemma
  fixes x y :: real
  assumes "is_limit u x"
          "is_upper_bound u y"
  shows   "x \<le> y"
proof (rule field_le_epsilon)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - x\<bar> < \<epsilon>"
    using assms(1) is_limit_def by auto
  then have "x < u k + \<epsilon>"
    by auto
  moreover have "u k \<le> y"
    using assms(2) is_upper_bound_def by simp
  ultimately show "x \<le> y + \<epsilon>"
    by simp
qed

(* Proof 3 *)
lemma
  fixes x y :: real
  assumes "is_limit u x"
          "is_upper_bound u y"
  shows   "x \<le> y"
proof (rule field_le_epsilon)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - x\<bar> < \<epsilon>"
    using assms(1) is_limit_def by auto
  then show "x \<le> y + \<epsilon>"
    using assms(2) is_upper_bound_def
    by (smt (verit) order_refl)
qed

end
