(* If_ff_is_biyective_then_f_is_biyective.thy
-- If f \<circ> f is bijective, then f is bijective.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, October 4, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove that if f \<sqdot> f is bijective, then f is bijective.
-- ------------------------------------------------------------------ *)

theory If_ff_is_biyective_then_f_is_biyective
imports Main
begin

(* Proof 1 *)
lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f"
  proof -
    have h1 : "inj (f \<circ> f)"
      using assms by (simp only: bij_is_inj)
    then show "inj f"
      by (simp only: inj_on_imageI2)
  qed
next
  show "surj f"
  proof -
    have h2 : "surj (f \<circ> f)"
      using assms by (simp only: bij_is_surj)
    then show "surj f"
      by auto
  qed
qed

(* Proof 2 *)
lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
proof (rule bijI)
  show "inj f"
    using assms bij_is_inj inj_on_imageI2
    by blast
next
  show "surj f"
    using assms bij_is_surj
    by fastforce
qed

(* Proof 3 *)
lemma
  assumes "bij (f \<circ> f)"
  shows   "bij f"
by (metis assms
          bij_betw_comp_iff
          bij_betw_def
          bij_betw_imp_surj
          inj_on_imageI2)

end
