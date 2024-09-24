(* Sum_of_powers_of_two.lean
-- Proofs of \<Sum>k<n. 2^k = 2^n-1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, September 24, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove that
--    1 + 2 + 2² + 2³ + ... + 2\<^sup>n⁾= 2\<^sup>n\<^sup>+\<^sup>1 - 1
-- ------------------------------------------------------------------ *)

theory Sum_of_powers_of_two
imports Main
begin

(* Proof 1 *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(\<Sum>k\<le>0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
  have "(\<Sum>k\<le>Suc n. (2::nat)^k) =
        (\<Sum>k\<le>n. (2::nat)^k) + 2^Suc n"
    by simp
  also have "\<dots> = (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  also have "\<dots> = 2^(Suc n + 1) - 1"
    by simp
  finally show "(\<Sum>k\<le>Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1" .
qed

(* Proof 2 *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(\<Sum>k\<le>0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
  have "(\<Sum>k\<le>Suc n. (2::nat)^k) =
        (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  then show "(\<Sum>k\<le>Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1"
    by simp
qed

(* Proof 3 *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* Proof 4 *)
lemma "(\<Sum>k\<le>n. (2::nat)^k) = 2^(n+1) - 1"
by (induct n) simp_all

end
