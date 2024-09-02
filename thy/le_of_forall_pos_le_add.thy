(* le_of_forall_pos_le_add.thy
-- If (\<forall> \<epsilon> > 0, y \<le> x + \<epsilon>), then y \<le> x
-- José A. Alonso <https://jaalonso.github.io>
-- Seville, September 2, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Let x, y \<in> \<real>. Prove that
--    (\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x
-- ------------------------------------------------------------------- *)

theory le_of_forall_pos_le_add
imports Main HOL.Real
begin

(* Proof 1 *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
proof (rule impI)
  assume h1 : "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>)"
  show "y \<le> x"
  proof (rule ccontr)
    assume "\<not> (y \<le> x)"
    then have "x < y"
      by simp
    then have "(y - x) / 2 > 0"
      by simp
    then have "y \<le> x + (y - x) / 2"
      using h1 by blast
    then have "2 * y \<le> 2 * x + (y - x)"
      by argo
    then have "y \<le> x"
      by simp
    then show False
      using \<open>\<not> (y \<le> x)\<close> by simp
  qed
qed

(* Proof 2 *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
proof (rule impI)
  assume h1 : "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>)"
  show "y \<le> x"
  proof (rule ccontr)
    assume "\<not> (y \<le> x)"
    then have "x < y"
      by simp
    then obtain z where hz : "x < z \<and> z < y"
      using Rats_dense_in_real by blast
    then have "0 < z -x"
      by simp
    then have "y \<le> x + (z - x)"
      using h1 by blast
    then have "y \<le> z"
      by simp
    then show False
      using hz by simp
  qed
qed

(* Proof 3 *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
proof (rule impI)
  assume h1 : "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>)"
  show "y \<le> x"
  proof (rule dense_le)
    fix z
    assume "z < y"
    then have "0 < y - z"
      by simp
    then have "y \<le> x + (y - z)"
      using h1 by simp
    then have "0 \<le> x - z"
      by simp
    then show "z \<le> x"
      by simp
  qed
qed

(* Proof 4 *)
lemma
  fixes x y :: real
  shows "(\<forall>\<epsilon>>0. y \<le> x + \<epsilon>) \<longrightarrow> y \<le> x"
  by (simp add: field_le_epsilon)

end
