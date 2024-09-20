(* Gauss_formula_for_summation.thy
-- Proofs of "\<Sum>_{i<n} i = n(n-1)/2"
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 19, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Gauss's formula for the sum of the first natural numbers is
--    0 + 1 + 2 + ... + (n-1) = n(n-1)/2
--
-- In a previous exercise, this formula was proven by induction. Another
-- way to prove it, without using induction, is as follows: The sum can
-- be written in two ways
--    S = 0     + 1     + 2     + ... + (n-3) + (n-2) + (n-1)
--    S = (n-1) + (n-2) + (n-3) + ... + 2     + 1     + 0
-- By adding them, we observe that each pair of numbers in the same
-- column sums to (n-1), and since there are n columns in total, it
-- follows that
--    2S = n(n-1)
-- which proves the formula.
--
-- Prove Gauss's formula by following the previous procedure.
-- ------------------------------------------------------------------ *)

theory Gauss_formula_for_summation
imports Main
begin

lemma
  fixes n :: nat
  shows "2 * (\<Sum>i<n. i) = n * (n - 1)"
proof -
  have "2 * (\<Sum>i<n. i) = (\<Sum>i<n. i) + (\<Sum>i<n. i)"
    by simp
  also have "\<dots> = (\<Sum>i<n. i) + (\<Sum>i<n. n - Suc i)"
    using sum.nat_diff_reindex [where g = id] by auto
  also have "\<dots> = (\<Sum>i<n. (i + (n - Suc i)))"
    using sum.distrib [where A = "{..<n}" and
                             g = id and
                             h = "\<lambda>i. n - Suc i"] by auto
  also have "\<dots> = (\<Sum>i<n. n - 1)"
    by simp
  also have "\<dots> = n * (n -1)"
    using sum_constant by auto
  finally show "2 * (\<Sum>i<n. i) = n * (n - 1)" .
qed

end
