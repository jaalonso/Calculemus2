(* Sum_of_the_first_n_natural_numbers.thy
-- Proofs of "0 + 1 + 2 + 3 + \<sqdot>\<sqdot>\<sqdot> + n = n \<times> (n + 1)/2"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 5, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove that the sum of the natural numbers
--    0 + 1 + 2 + 3 + \<sqdot>\<sqdot>\<sqdot> + n
-- is n \<times> (n + 1)/2
-- ------------------------------------------------------------------ *)

theory Sum_of_the_first_n_natural_numbers
imports Main
begin

fun sum :: "nat \<Rightarrow> nat" where
  "sum 0       = 0"
| "sum (Suc n) = sum n + Suc n"

(* Proof 1 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  have "2 * sum 0 = 2 * 0"
    by (simp only: sum.simps(1))
  also have "\<dots> = 0"
    by (rule mult_0_right)
  also have "\<dots> = 0 * (0 + 1)"
    by (rule mult_0 [symmetric])
  finally show "2 * sum 0 = 0 * (0 + 1)"
    by this
next
  fix n
  assume HI : "2 * sum n = n * (n + 1)"
  have "2 * sum (Suc n) = 2 * (sum n + Suc n)"
    by (simp only: sum.simps(2))
  also have "\<dots> = 2 * sum n + 2 * Suc n"
    by (rule add_mult_distrib2)
  also have "\<dots> = n * (n + 1) + 2 * Suc n"
    by (simp only: HI)
  also have "\<dots> = n * (n + Suc 0) + 2 * Suc n"
    by (simp only: One_nat_def)
  also have "\<dots> = n * Suc (n + 0) + 2 * Suc n"
    by (simp only: add_Suc_right)
  also have "\<dots> = n * Suc n + 2 * Suc n"
    by (simp only: add_0_right)
  also have "\<dots> = (n + 2) * Suc n"
    by (simp only: add_mult_distrib)
  also have "\<dots> = Suc (Suc n) * Suc n"
    by (simp only: add_2_eq_Suc')
  also have "\<dots> = (Suc n + 1) * Suc n"
    by (simp only: Suc_eq_plus1)
  also have "\<dots> = Suc n * (Suc n + 1)"
    by (simp only: mult.commute)
  finally show "2 * sum (Suc n) = Suc n * (Suc n + 1)"
    by this
qed

(* Proof 2 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  have "2 * sum 0 = 2 * 0" by simp
  also have "\<dots> = 0" by simp
  also have "\<dots> = 0 * (0 + 1)" by simp
  finally show "2 * sum 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * sum n = n * (n + 1)"
  have "2 * sum (Suc n) = 2 * (sum n + Suc n)" by simp
  also have "\<dots> = 2 * sum n + 2 * Suc n" by simp
  also have "\<dots> = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "\<dots> = n * (n + Suc 0) + 2 * Suc n" by simp
  also have "\<dots> = n * Suc (n + 0) + 2 * Suc n" by simp
  also have "\<dots> = n * Suc n + 2 * Suc n" by simp
  also have "\<dots> = (n + 2) * Suc n" by simp
  also have "\<dots> = Suc (Suc n) * Suc n" by simp
  also have "\<dots> = (Suc n + 1) * Suc n" by simp
  also have "\<dots> = Suc n * (Suc n + 1)" by simp
  finally show "2 * sum (Suc n) = Suc n * (Suc n + 1)" .
qed

(* Proof 3 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  have "2 * sum 0 = 2 * 0" by simp
  also have "\<dots> = 0" by simp
  also have "\<dots> = 0 * (0 + 1)" by simp
  finally show "2 * sum 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * sum n = n * (n + 1)"
  have "2 * sum (Suc n) = 2 * (sum n + Suc n)" by simp
  also have "\<dots> = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "\<dots> = (n + 2) * Suc n" by simp
  also have "\<dots> = Suc n * (Suc n + 1)" by simp
  finally show "2 * sum (Suc n) = Suc n * (Suc n + 1)" .
qed

(* Proof 4 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  show "2 * sum 0 = 0 * (0 + 1)" by simp
next
  fix n
  assume "2 * sum n = n * (n + 1)"
  then show "2 * sum (Suc n) = Suc n * (Suc n + 1)" by simp
qed

(* Proof 5 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* Proof 6 *)
lemma
  "2 * sum n = n * (n + 1)"
by (induct n) simp_all

end
