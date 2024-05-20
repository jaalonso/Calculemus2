(* Una_funcion_creciente_e_involutiva_es_la_identidad.thy
-- Si una función es creciente e involutiva, entonces es la identidad
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea una función f de \<real> en \<real>.
-- + Se dice que f es creciente si para todo x e y tales que x \<le> y se
--   tiene que f(x) \<le> f(y).
-- + Se dice que f es involutiva si para todo x se tiene que f(f(x)) = x.
--
-- En Isabelle/HOL que f sea creciente se representa por `mono f`.
--
-- Demostrar que si f es creciente e involutiva, entonces f es la
-- identidad.
-- ------------------------------------------------------------------ *)

theory Una_funcion_creciente_e_involutiva_es_la_identidad
imports Main HOL.Real
begin

definition involutiva :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "involutiva f \<longleftrightarrow> (\<forall>x. f (f x) = x)"

(* 1\<ordfeminine> demostración *)

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof (unfold fun_eq_iff; intro allI)
  fix x
  have "x \<le> f x \<or> f x \<le> x"
    by (rule linear)
  then have "f x = x"
  proof (rule disjE)
    assume "x \<le> f x"
    then have "f x \<le> f (f x)"
      using assms(1) by (simp only: monoD)
    also have "\<dots> = x"
      using assms(2) by (simp only: involutiva_def)
    finally have "f x \<le> x"
      by this
    show "f x = x"
      using \<open>f x \<le> x\<close> \<open>x \<le> f x\<close> by (simp only: antisym)
  next
    assume "f x \<le> x"
    have "x = f (f x)"
      using assms(2) by (simp only: involutiva_def)
    also have "... \<le> f x"
      using \<open>f x \<le> x\<close> assms(1) by (simp only: monoD)
    finally have "x \<le> f x"
      by this
    show "f x = x"
      using \<open>f x \<le> x\<close> \<open>x \<le> f x\<close> by (simp only: monoD)
  qed
  then show "f x = id x"
    by (simp only: id_apply)
qed

(* 2\<ordfeminine> demostración *)

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof
  fix x
  have "x \<le> f x \<or> f x \<le> x"
    by (rule linear)
  then have "f x = x"
  proof
    assume "x \<le> f x"
    then have "f x \<le> f (f x)"
      using assms(1) by (simp only: monoD)
    also have "\<dots> = x"
      using assms(2) by (simp only: involutiva_def)
    finally have "f x \<le> x"
      by this
    show "f x = x"
      using \<open>f x \<le> x\<close> \<open>x \<le> f x\<close> by auto
  next
    assume "f x \<le> x"
    have "x = f (f x)"
      using assms(2) by (simp only: involutiva_def)
    also have "... \<le> f x"
      by (simp add: \<open>f x \<le> x\<close> assms(1) monoD)
    finally have "x \<le> f x"
      by this
    show "f x = x"
      using \<open>f x \<le> x\<close> \<open>x \<le> f x\<close> by auto
  qed
  then show "f x = id x"
    by simp
qed

(* 3\<ordfeminine> demostración *)

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof
  fix x
  have "x \<le> f x \<or> f x \<le> x"
    by (rule linear)
  then have "f x = x"
  proof
    assume "x \<le> f x"
    then have "f x \<le> x"
      by (metis assms involutiva_def mono_def)
    then show "f x = x"
      using \<open>x \<le> f x\<close> by auto
  next
    assume "f x \<le> x"
    then have "x \<le> f x"
      by (metis assms involutiva_def mono_def)
    then show "f x = x"
      using \<open>f x \<le> x\<close> by auto
  qed
  then show "f x = id x"
    by simp
qed

end
