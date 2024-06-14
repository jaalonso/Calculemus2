(* Las_funciones_con_inversa_son_biyectivas.thy
-- Las funciones con inversa son biyectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle se puede definir que g es una inversa de f por
--    definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
--      "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"
-- y que f tiene inversa por
--    definition tiene_inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa f \<longleftrightarrow> (\<exists> g. inversa f g)"
--
-- Demostrar que si la función f tiene inversa, entonces f es biyectiva.
-- ------------------------------------------------------------------ *)

theory Las_funciones_con_inversa_son_biyectivas
imports Main
begin

definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"

definition tiene_inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa f \<longleftrightarrow> (\<exists> g. inversa f g)"

(* 1\<ordfeminine> demostración *)

lemma
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "tiene_inversa f"
  shows   "bij f"
proof -
  obtain g where h1 : "\<forall> x. (g \<circ> f) x = x" and
                 h2 : "\<forall> y. (f \<circ> g) y = y"
    by (meson assms inversa_def tiene_inversa_def)
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "tiene_inversa f"
  shows   "bij f"
proof -
  obtain g where h1 : "\<forall> x. (g \<circ> f) x = x" and
                 h2 : "\<forall> y. (f \<circ> g) y = y"
    by (meson assms inversa_def tiene_inversa_def)
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
qed

end
