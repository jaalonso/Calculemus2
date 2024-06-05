(* La_congruencia_modulo_2_es_una_relacion_de_equivalencia.thy
-- La congruencia módulo 2 es una relación de equivalencia
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Se define la relación R entre los números enteros de forma que x está
-- relacionado con y si x-y es divisible por 2. Demostrar que R es una
-- relación de equivalencia.
-- ------------------------------------------------------------------ *)

theory La_congruencia_modulo_2_es_una_relacion_de_equivalencia
imports Main
begin

definition R :: "(int \<times> int) set" where
  "R = {(m, n). even (m - n)}"

lemma R_iff [simp]:
  "((x, y) \<in> R) = even (x - y)"
by (simp add: R_def)

(* 1\<ordfeminine> demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show "R \<subseteq> UNIV \<times> UNIV"
    proof -
      have "R \<subseteq> UNIV"
        by (rule top.extremum)
      also have "\<dots> = UNIV \<times> UNIV"
        by (rule Product_Type.UNIV_Times_UNIV[symmetric])
      finally show "R \<subseteq> UNIV \<times> UNIV"
        by this
    qed
  next
    show "\<forall>x\<in>UNIV. (x, x) \<in> R"
    proof
      fix x :: int
      assume "x \<in> UNIV"
      have "even 0" by (rule even_zero)
      then have "even (x - x)" by (simp only: diff_self)
      then show "(x, x) \<in> R"
        by (simp only: R_iff)
    qed
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y :: int
    assume "(x, y) \<in> R"
    then have "even (x - y)"
      by (simp only: R_iff)
    then show "(y, x) \<in> R"
    proof (rule evenE)
      fix a :: int
      assume ha : "x - y = 2 * a"
      have "y - x = -(x - y)"
        by (rule minus_diff_eq[symmetric])
      also have "\<dots> = -(2 * a)"
        by (simp only: ha)
      also have "\<dots> = 2 * (-a)"
        by (rule mult_minus_right[symmetric])
      finally have "y - x = 2 * (-a)"
        by this
      then have "even (y - x)"
        by (rule dvdI)
      then show "(y, x) \<in> R"
        by (simp only: R_iff)
    qed
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume hxy : "(x, y) \<in> R" and hyz : "(y, z) \<in> R"
    have "even (x - y)"
      using hxy by (simp only: R_iff)
    then obtain a where ha : "x - y = 2 * a"
      by (rule dvdE)
    have "even (y - z)"
      using hyz by (simp only: R_iff)
    then obtain b where hb : "y - z = 2 * b"
      by (rule dvdE)
    have "x - z = (x - y) + (y - z)"
      by simp
    also have "\<dots> = (2 * a) + (2 * b)"
      by (simp only: ha hb)
    also have "\<dots> = 2 * (a + b)"
      by (simp only: distrib_left)
    finally have "x - z = 2 * (a + b)"
      by this
    then have "even (x - z)"
      by (rule dvdI)
    then show "(x, z) \<in> R"
      by (simp only: R_iff)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show "R \<subseteq> UNIV \<times> UNIV" by simp
  next
    show "\<forall>x\<in>UNIV. (x, x) \<in> R"
    proof
      fix x :: int
      assume "x \<in> UNIV"
      have "x - x = 2 * 0"
        by simp
      then show "(x, x) \<in> R"
        by simp
    qed
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y :: int
    assume "(x, y) \<in> R"
    then have "even (x - y)"
      by simp
    then obtain a where ha : "x - y = 2 * a"
      by blast
    then have "y - x = 2 *(-a)"
      by simp
    then show "(y, x) \<in> R"
      by simp
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume hxy : "(x, y) \<in> R" and hyz : "(y, z) \<in> R"
    have "even (x - y)"
      using hxy by simp
    then obtain a where ha : "x - y = 2 * a"
      by blast
    have "even (y - z)"
      using hyz by simp
    then obtain b where hb : "y - z = 2 * b"
      by blast
    have "x - z = 2 * (a + b)"
      using ha hb by auto
    then show "(x, z) \<in> R"
      by simp
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show " R \<subseteq> UNIV \<times> UNIV"
      by simp
  next
    show "\<forall>x\<in>UNIV. (x, x) \<in> R"
      by simp
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y
    assume "(x, y) \<in> R"
    then show "(y, x) \<in> R"
      by simp
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume "(x, y) \<in> R" and "(y, z) \<in> R"
    then show "(x, z) \<in> R"
      by simp
  qed
qed

(* 4\<ordfeminine> demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
    unfolding refl_on_def by simp
next
  show "sym R"
    unfolding sym_def by simp
next
  show "trans R"
    unfolding trans_def by simp
qed

(* 5\<ordfeminine> demostración *)

lemma "equiv UNIV R"
  unfolding equiv_def refl_on_def sym_def trans_def
  by simp

(* 6\<ordfeminine> demostración *)

lemma "equiv UNIV R"
  by (simp add: equiv_def refl_on_def sym_def trans_def)

end
