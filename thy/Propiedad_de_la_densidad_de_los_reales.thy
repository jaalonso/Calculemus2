(* Propiedad_de_la_densidad_de_los_reales.thy
-- Si x, y \<in> \<real> tales que (\<forall> z)[y < z \<rightarrow> x \<le> z], entonces x \<le> y
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean x, y números reales tales que
--    \<forall> z, y < z \<rightarrow> x \<le> z
-- Demostrar que x \<le> y.
-- ------------------------------------------------------------------ *)

theory Propiedad_de_la_densidad_de_los_reales
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)

lemma
  fixes x y :: real
  assumes "\<forall> z. y < z \<longrightarrow> x \<le> z"
  shows "x \<le> y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "\<exists>z. y < z \<and> z < x"
    by (rule dense)
  then obtain a where ha : "y < a \<and> a < x"
    by (rule exE)
  have "\<not> a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
  proof -
    have "y < a \<longrightarrow> x \<le> a"
      using assms by (rule allE)
    moreover
    have "y < a"
      using ha by (rule conjunct1)
    ultimately have "x \<le> a"
      by (rule mp)
    moreover
    have "a < x"
      using ha by (rule conjunct2)
    ultimately show "a < a"
      by (simp only: less_le_trans)
  qed
  ultimately show False
    by (rule notE)
qed

(* 2\<ordfeminine> demostración *)

lemma
  fixes x y :: real
  assumes "\<And> z. y < z \<Longrightarrow> x \<le> z"
  shows "x \<le> y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "\<exists>z. y < z \<and> z < x"
    by (rule dense)
  then obtain a where hya : "y < a" and hax : "a < x"
    by auto
  have "\<not> a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
  proof -
    have "a < x"
      using hax .
    also have "\<dots> \<le> a"
      using assms[OF hya] .
    finally show "a < a" .
  qed
  ultimately show False
    by (rule notE)
qed

(* 3\<ordfeminine> demostración *)

lemma
  fixes x y :: real
  assumes "\<And> z. y < z \<Longrightarrow> x \<le> z"
  shows "x \<le> y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "\<exists>z. y < z \<and> z < x"
    by (rule dense)
  then obtain a where hya : "y < a" and hax : "a < x"
    by auto
  have "\<not> a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
    using hax assms[OF hya] by (rule less_le_trans)
  ultimately show False
    by (rule notE)
qed

(* 4\<ordfeminine> demostración *)

lemma
  fixes x y :: real
  assumes "\<And> z. y < z \<Longrightarrow> x \<le> z"
  shows "x \<le> y"
by (meson assms dense not_less)

(* 5\<ordfeminine> demostración *)

lemma
  fixes x y :: real
  assumes "\<And> z. y < z \<Longrightarrow> x \<le> z"
  shows "x \<le> y"
using assms by (rule dense_ge)

(* 6\<ordfeminine> demostración *)

lemma
  fixes x y :: real
  assumes "\<forall> z. y < z \<longrightarrow> x \<le> z"
  shows "x \<le> y"
using assms by (simp only: dense_ge)

end
