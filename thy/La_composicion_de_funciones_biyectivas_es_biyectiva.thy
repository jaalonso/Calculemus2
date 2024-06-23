(* La_composicion_de_funciones_biyectivas_es_biyectiva.thy
-- La composición de funciones biyectivas es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones biyectivas es una
-- función biyectiva.
-- ------------------------------------------------------------------ *)

theory La_composicion_de_funciones_biyectivas_es_biyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g \<circ> f)"
proof (rule bijI)
  show "inj (g \<circ> f)"
  proof (rule inj_compose)
    show "inj g"
      using \<open>bij g\<close> by (rule bij_is_inj)
  next
    show "inj f"
      using \<open>bij f\<close> by (rule bij_is_inj)
  qed
next
  show "surj (g \<circ> f)"
  proof (rule comp_surj)
    show "surj f"
      using \<open>bij f\<close> by (rule bij_is_surj)
  next
    show "surj g"
      using \<open>bij g\<close> by (rule bij_is_surj)
  qed
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g \<circ> f)"
proof (rule bijI)
  show "inj (g \<circ> f)"
  proof (rule inj_compose)
    show "inj g"
      by (rule bij_is_inj [OF \<open>bij g\<close>])
  next
    show "inj f"
      by (rule bij_is_inj [OF \<open>bij f\<close>])
  qed
next
  show "surj (g \<circ> f)"
  proof (rule comp_surj)
    show "surj f"
      by (rule bij_is_surj [OF \<open>bij f\<close>])
  next
    show "surj g"
      by (rule bij_is_surj [OF \<open>bij g\<close>])
  qed
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g \<circ> f)"
proof (rule bijI)
  show "inj (g \<circ> f)"
    by (rule inj_compose [OF bij_is_inj [OF \<open>bij g\<close>]
                             bij_is_inj [OF \<open>bij f\<close>]])
next
  show "surj (g \<circ> f)"
    by (rule comp_surj [OF bij_is_surj [OF \<open>bij f\<close>]
                           bij_is_surj [OF \<open>bij g\<close>]])
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g \<circ> f)"
by (rule bijI [OF inj_compose [OF bij_is_inj  [OF \<open>bij g\<close>]
                                  bij_is_inj  [OF \<open>bij f\<close>]]
                  comp_surj   [OF bij_is_surj [OF \<open>bij f\<close>]
                                  bij_is_surj [OF \<open>bij g\<close>]]])

(* 5\<ordfeminine> demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g \<circ> f)"
using assms
by (rule bij_comp)

(* Nota: Auto solve indica la demostración anterior. *)

end
