(* Sufficient_condition_of_continuity.thy
-- If f is continuous at a and the limit of u(n) is a, then the limit of f(u(n)) is f(a).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 4, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL, we can define that a is the limit of the sequence u
-- by:
--    definition is_limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "is_limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> \<le> \<epsilon>)"
-- and that f is continuous at a by:
--    definition continuous_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "continuous_at f a \<longleftrightarrow>
--       (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
--
-- To prove that if the function f is continuous at the point a, and the
-- sequence u(n) converges to a, then the sequence f(u(n)) converges to
-- f(a).
-- ------------------------------------------------------------------ *)

theory Sufficient_condition_of_continuity
imports Main HOL.Real
begin

definition is_limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "is_limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> \<le> \<epsilon>)"

definition continuous_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "continuous_at f a \<longleftrightarrow>
   (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"

(* Proof 1 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f \<circ> u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where h\<delta>1 : "\<delta> > 0" and
                      h\<delta>2 :" (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continuous_at_def by auto
  obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) is_limite_def h\<delta>1 by auto
  have "\<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
  proof (intro allI impI)
    fix n
    assume "n \<ge> k"
    then have "\<bar>u n - a\<bar> \<le> \<delta>"
      using hk by auto
    then show "\<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
      using h\<delta>2 by simp
  qed
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    by auto
qed

(* Proof 2 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f \<circ> u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where h\<delta>1 : "\<delta> > 0" and
                      h\<delta>2 :" (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continuous_at_def by auto
  obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) is_limite_def h\<delta>1 by auto
  have "\<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    using hk h\<delta>2 by simp
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    by auto
qed

(* Proof 3 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f \<circ> u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where h\<delta>1 : "\<delta> > 0" and
                      h\<delta>2 :" (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continuous_at_def by auto
  obtain k where hk : "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) is_limite_def h\<delta>1 by auto
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    using hk h\<delta>2 by auto
qed

(* Proof 4 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f \<circ> u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then obtain \<delta> where
              h\<delta> : "\<delta> > 0 \<and> (\<forall>x. \<bar>x - a\<bar> \<le> \<delta> \<longrightarrow> \<bar>f x - f a\<bar> \<le> \<epsilon>)"
    using assms(1) continuous_at_def by auto
  then obtain k where "\<forall>n\<ge>k. \<bar>u n - a\<bar> \<le> \<delta>"
    using assms(2) is_limite_def by auto
  then show "\<exists>k. \<forall>n\<ge>k. \<bar>(f \<circ> u) n - f a\<bar> \<le> \<epsilon>"
    using h\<delta> by auto
qed

(* Proof 5 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f \<circ> u) (f a)"
  using assms continuous_at_def is_limite_def
  by force

end
