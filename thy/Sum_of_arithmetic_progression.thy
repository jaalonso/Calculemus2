(* Sum_of_arithmetic_progression.thy
-- Proofs of a+(a+d)+(a+2d)+\<sqdot>\<sqdot>\<sqdot>+(a+nd)=(n+1)(2a+nd)/2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 7, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove that the sum of the terms of the arithmetic progression
--    a + (a + d) + (a + 2 × d) + ··· + (a + n × d)
-- is (n + 1) × (2 × a + n × d) / 2.
-- ------------------------------------------------------------------ *)

theory Sum_of_arithmetic_progression
imports Main HOL.Real
begin

fun sumAP :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "sumAP a d 0 = a"
| "sumAP a d (Suc n) = sumAP a d n + (a + (n + 1) * d)"

(* Proof 1 *)
lemma
  "2 * sumAP a d n = (n + 1) * (2 * a + n * d)"
proof (induct n)
  show "2 * sumAP a d 0 =
        (real 0 + 1) * (2 * a + real 0 * d)"
    by simp
next
  fix n
  assume IH : "2 * sumAP a d n =
               (n + 1) * (2 * a + n * d)"
  have "2 * sumAP a d (Suc n) =
        2 * (sumAP a d n + (a + (n + 1) * d))"
    by simp
  also have "\<dots> = 2 * sumAP a d n + 2 * (a + (n + 1) * d)"
    by simp
  also have "\<dots> = (n + 1) * (2 * a + n * d) + 2 * (a + (n + 1) * d)"
    using IH by simp
  also have "\<dots> = (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by (simp add: algebra_simps)
  finally show "2 * sumAP a d (Suc n) =
                (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by this
qed

(* Proof 2 *)
lemma
  "2 * sumAP a d n = (n + 1) * (2*a + n*d)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: algebra_simps)
qed

(* Proof 3 *)
lemma
  "2 * sumAP a d n = (n + 1) * (2*a + n*d)"
by (induct n) (simp_all add: algebra_simps)

end
