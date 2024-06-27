(* La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.thy
-- La composición por la izquierda con una inyectiva es una operación inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean f₁ y f₂ funciones de X en Y y g una función de X en Y. Demostrar
-- que si g es inyectiva y g \<circ> f₁ = g \<circ> f₂, entonces f₁ = f₂.
-- ------------------------------------------------------------------ *)

theory La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
proof (rule ext)
  fix x
  have "(g \<circ> f1) x = (g \<circ> f2) x"
    using \<open>g \<circ> f1 = g \<circ> f2\<close> by (rule fun_cong)
  then have "g (f1 x) = g (f2 x)"
    by (simp only: o_apply)
  then show "f1 x = f2 x"
    using \<open>inj g\<close> by (simp only: injD)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
proof
  fix x
  have "(g \<circ> f1) x = (g \<circ> f2) x"
    using \<open>g \<circ> f1 = g \<circ> f2\<close> by simp
  then have "g (f1 x) = g (f2 x)"
    by simp
  then show "f1 x = f2 x"
    using \<open>inj g\<close> by (simp only: injD)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
using assms
by (metis fun.inj_map_strong inj_eq)

(* 4\<ordfeminine> demostración *)

lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
proof -
  have "f1 = id \<circ> f1"
    by (rule id_o [symmetric])
  also have "\<dots> = (inv g \<circ> g) \<circ> f1"
    by (simp add: assms(1))
  also have "\<dots> = inv g \<circ> (g \<circ> f1)"
    by (simp add: comp_assoc)
  also have "\<dots> = inv g \<circ> (g \<circ> f2)"
    using assms(2) by (rule arg_cong)
  also have "\<dots> = (inv g \<circ> g) \<circ> f2"
    by (simp add: comp_assoc)
  also have "\<dots> = id \<circ> f2"
    by (simp add: assms(1))
  also have "\<dots> = f2"
    by (rule id_o)
  finally show "f1 = f2"
    by this
qed

(* 5\<ordfeminine> demostración *)

lemma
  assumes "inj g"
          "g \<circ> f1 = g \<circ> f2"
  shows   "f1 = f2"
proof -
  have "f1 = (inv g \<circ> g) \<circ> f1"
    by (simp add: assms(1))
  also have "\<dots> = (inv g \<circ> g) \<circ> f2"
    using assms(2) by (simp add: comp_assoc)
  also have "\<dots> = f2"
    using assms(1) by simp
  finally show "f1 = f2" .
qed

end
