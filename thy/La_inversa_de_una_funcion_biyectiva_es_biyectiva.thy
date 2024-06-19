(* La_inversa_de_una_funcion_biyectiva_es_biyectiva.thy
-- La inversa de una función biyectiva es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle se puede definir que g es una inversa de f por
--    definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
--      "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"
--
-- Demostrar que si la función f es biyectiva y g es una inversa de f,
-- entonces g es biyectiva.
-- ------------------------------------------------------------------- *)

theory La_inversa_de_una_funcion_biyectiva_es_biyectiva
imports Main
begin

definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"

(* 1\<ordfeminine> demostración *)

lemma
  fixes   f :: "'a \<Rightarrow> 'b"
  assumes "inversa g f"
  shows   "bij g"
proof (rule bijI)
  show "inj g"
  proof (rule injI)
    fix x y
    assume "g x = g y"
    have h1 : "\<forall> y. (f \<circ> g) y = y"
      by (meson assms inversa_def)
    then have "x = (f \<circ> g) x"
      by (simp only: allE)
    also have "\<dots> = f (g x)"
      by (simp only: o_apply)
    also have "\<dots> = f (g y)"
      by (simp only: \<open>g x = g y\<close>)
    also have "\<dots> = (f \<circ> g) y"
      by (simp only: o_apply)
    also have "\<dots> = y"
      using h1 by (simp only: allE)
    finally show "x = y"
      by this
  qed
next
  show "surj g"
  proof (rule surjI)
    fix x
    have h2 : "\<forall> x. (g \<circ> f) x = x"
      by (meson assms inversa_def)
    then have "(g \<circ> f) x = x"
      by (simp only: allE)
    then show "g (f x) = x"
      by (simp only: o_apply)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  fixes   f :: "'a \<Rightarrow> 'b"
  assumes "inversa g f"
  shows   "bij g"
proof (rule bijI)
  show "inj g"
  proof (rule injI)
    fix x y
    assume "g x = g y"
    have h1 : "\<forall> y. (f \<circ> g) y = y"
      by (meson assms inversa_def)
    then show "x = y"
      by (metis \<open>g x = g y\<close> o_apply)
  qed
next
  show "surj g"
  proof (rule surjI)
    fix x
    have h2 : "\<forall> x. (g \<circ> f) x = x"
      by (meson assms inversa_def)
    then show "g (f x) = x"
      by (simp only: o_apply)
  qed
qed

end
