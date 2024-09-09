(* Sum_of_geometric_progresion.lean
-- Proofs of a+aq+aq²+\<sqdot>\<sqdot>\<sqdot>+aqⁿ = a(1-qⁿ⁺¹)/(1-q)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-septiembre-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove that if q \<noteq> 1, then the sum of the terms of the
-- geometric progression
--    a + aq + aq² + \<sqdot>\<sqdot>\<sqdot> + aq\<^sup>nⁿ
-- is
--      a(1 - q\<^sup>n\<^sup>+\<^sup>1)
--    -------------
--        1 - q
-- ------------------------------------------------------------------ *)

theory Sum_of_geometric_progresion
imports Main HOL.Real
begin

fun sumGP :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "sumGP a q 0 = a"
| "sumGP a q (Suc n) = sumGP a q n + (a * q^(n + 1))"

(* Proof 1 *)
lemma
  "(1 - q) * sumGP a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume IH : "(1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumGP a q (Suc n) =
        (1 - q) * (sumGP a q n + (a * q^(n + 1)))"
    by simp
  also have "\<dots> = (1 - q) * sumGP a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using IH by simp
  also have "\<dots> = a * (1 - q ^ (n + 1) + (1 - q) * q^(n + 1))"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q^(n + 2))"
    by simp
  also have "\<dots> = a * (1 - q ^ (Suc n + 1))"
    by simp
  finally show "(1 - q) * sumGP a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by this
qed

(* Proof 2 *)
lemma
  "(1 - q) * sumGP a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume IH : "(1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumGP a q (Suc n) =
        (1 - q) * sumGP a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "\<dots> = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using IH by simp
  also have "\<dots> = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  finally show "(1 - q) * sumGP a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by simp
qed

(* Proof 3 *)
lemma
  "(1 - q) * sumGP a q n = a * (1 - q^(n + 1))"
  using power_add
  by (induct n) (auto simp: algebra_simps)

end
