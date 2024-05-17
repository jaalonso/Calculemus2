(* La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.thy
-- La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.lean
-- La composición de una función creciente y una decreciente es decreciente
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea una función f de \<real> en \<real>. Se dice que f es creciente si para todo
-- x e y tales que x \<le> y se tiene  que f(x) \<le> f(y). Se dice que f es
-- decreciente si para todo x e y tales que x \<le> y se tiene que
-- f(x) \<ge> f(y).
--
-- En Isabelle/HOL que f sea creciente se representa por `mono f` y que
-- sea decreciente por `antimono f`.
--
-- Demostrar que si f es creciente y g es decreciente, entonces (g \<circ> f)
-- es decreciente.
-- ------------------------------------------------------------------ *)

theory La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)

lemma
  fixes f g :: "real \<Rightarrow> real"
  assumes "mono f"
          "antimono g"
  shows   "antimono (g \<circ> f)"
proof (rule antimonoI)
  fix x y :: real
  assume "x \<le> y"
  have "(g \<circ> f) y = g (f y)"
    by (simp only: o_apply)
  also have "\<dots> \<le> g (f x)"
    using assms \<open>x \<le> y\<close>
    by (metis antimonoE monoD)
  also have "\<dots> = (g \<circ> f) x"
    by (simp only: o_apply)
  finally show "(g \<circ> f) x \<ge> (g \<circ> f) y"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  fixes f g :: "real \<Rightarrow> real"
  assumes "mono f"
          "antimono g"
  shows   "antimono (g \<circ> f)"
proof (rule antimonoI)
  fix x y :: real
  assume "x \<le> y"
  have "(g \<circ> f) y = g (f y)"    by simp
  also have "\<dots> \<le> g (f x)"     by (meson \<open>x \<le> y\<close> assms antimonoE monoE)
  also have "\<dots> = (g \<circ> f) x"    by simp
  finally show "(g \<circ> f) x \<ge> (g \<circ> f) y" .
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "mono f"
          "antimono g"
  shows   "antimono (g \<circ> f)"
  using assms(1) assms(2) monotone_on_o 
  by blast
  
end
