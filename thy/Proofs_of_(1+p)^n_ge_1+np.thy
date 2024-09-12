(* Proofs_of_(1+p)^n_ge_1+np.lean
-- Proofs of "If p > -1, then (1+p)ⁿ ≥ 1+np"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 12, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Let p ∈ ℝ and n ∈ ℕ. Prove that if p > -1, then
--    (1 + p)^n \<ge> 1 + n*p
-- ------------------------------------------------------------------ *)

theory "Proofs_of_(1+p)^n_ge_1+np"
imports Main HOL.Real
begin

lemma
  fixes p :: real
  assumes "p > -1"
  shows "(1 + p)^n \<ge> 1 + n*p"
proof (induct n)
  show "(1 + p) ^ 0 \<ge> 1 + real 0 * p"
    by simp
next
  fix n
  assume IH : "(1 + p)^n \<ge> 1 +  n * p"
  have "1 + Suc n * p = 1 + (n + 1) * p"
    by simp
  also have "\<dots> = 1 + n*p + p"
    by (simp add: distrib_right)
  also have "\<dots> \<le> (1 + n*p + p) + n*(p*p)"
    by simp
  also have "\<dots> = (1 + n * p) * (1 + p)"
    by algebra
  also have "\<dots> \<le> (1 + p)^n * (1 + p)"
    using IH assms by simp
  also have "\<dots> = (1 + p)^(Suc n)"
    by simp
  finally show "1 + Suc n * p \<le> (1 + p)^(Suc n)" .
qed

end
