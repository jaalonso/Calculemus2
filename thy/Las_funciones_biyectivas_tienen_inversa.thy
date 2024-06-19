(* Las_funciones_biyectivas_tienen_inversa.thy
-- Las funciones biyectivas tienen inversa.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle se puede definir que g es una inversa de f por
--    definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
--      "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"
-- y que f tiene inversa por
--    definition tiene_inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa f \<longleftrightarrow> (\<exists> g. inversa f g)"
--
-- Demostrar que si la función f es biyectiva, entonces f tiene inversa.
-- ------------------------------------------------------------------ *)

theory Las_funciones_biyectivas_tienen_inversa
imports Main
begin

definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"

definition tiene_inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa f \<longleftrightarrow> (\<exists> g. inversa f g)"

(* 1\<ordfeminine> demostración *)

lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "surj f"
    using assms by (rule bij_is_surj)
  then obtain g where hg : "\<forall>y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "\<forall>x. (g \<circ> f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using \<open>bij f\<close> by (rule bij_is_inj)
      then show "(g \<circ> f) x = x"
      proof (rule injD)
        have "f ((g \<circ> f) x) = f (g (f x))"
          by simp
        also have "\<dots> = f x"
          by (simp add: hg)
        finally show "f ((g \<circ> f) x) = f x"
          by this
      qed
    qed
    next
      show "\<forall>y. (f \<circ> g) y = y"
        by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by blast
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "surj f"
    using assms by (rule bij_is_surj)
  then obtain g where hg : "\<forall>y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "\<forall>x. (g \<circ> f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using \<open>bij f\<close> by (rule bij_is_inj)
      then show "(g \<circ> f) x = x"
      proof (rule injD)
        have "f ((g \<circ> f) x) = f (g (f x))"
          by simp
        also have "\<dots> = f x"
          by (simp add: hg)
        finally show "f ((g \<circ> f) x) = f x"
          by this
      qed
    qed
  next
    show "\<forall>y. (f \<circ> g) y = y"
      by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "inversa f (inv f)"
  proof (unfold inversa_def; intro conjI)
    show "\<forall>x. (inv f \<circ> f) x = x"
      by (simp add: \<open>bij f\<close> bij_is_inj)
  next
    show "\<forall>y. (f \<circ> inv f) y = y"
      by (simp add: \<open>bij f\<close> bij_is_surj surj_f_inv_f)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

end
