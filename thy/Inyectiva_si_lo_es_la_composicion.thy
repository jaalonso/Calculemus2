(* Inyectiva_si_lo_es_la_composicion.thy
-- Si g \<circ> f es inyectiva, entonces f es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sean f: X \<rightarrow> Y y g: Y \<rightarrow> Z. Demostrar que si g \<circ> f es inyectiva,
-- entonces f es inyectiva.
-- ------------------------------------------------------------------- *)

theory Inyectiva_si_lo_es_la_composicion
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "inj (g \<circ> f)"
  shows "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  show "x = y"
  proof -
    have "g (f x) = g (f y)"
      using \<open>f x = f y\<close>
      by simp
    then have "(g \<circ> f) x = (g \<circ> f) y"
      by simp
    with assms show "x = y"
      by (rule injD) 
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "inj (g \<circ> f)"
  shows "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  then show "x = y"
    using assms injD by fastforce
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "inj (g \<circ> f)"
  shows "inj f"
using assms
by (rule inj_on_imageI2)

(* Nota: Al calcular el cursor en shows sale una sugerencia indicando
   que se puede demostrar con la regla inj_on_imageI2. *)

end
