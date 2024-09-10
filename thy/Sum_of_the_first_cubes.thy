(* Sum_of_the_first_cubes.thy
-- Proofs of 0³+1³+2³+3³+\<sqdot>\<sqdot>\<sqdot>+n³ = (n(n+1)/2)²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 10, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove that the sum of the first cubes
--    0³ + 1³ + 2³ + 3³ + \<sqdot>\<sqdot>\<sqdot> + n³
-- is (n(n+1)/2)²
-- ------------------------------------------------------------------ *)

theory Sum_of_the_first_cubes
imports Main
begin

fun sumCubes :: "nat \<Rightarrow> nat" where
  "sumCubes 0       = 0"
| "sumCubes (Suc n) = sumCubes n + (Suc n)^3"

(* Proof 1 *)
lemma
  "4 * sumCubes n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumCubes 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume IH : "4 * sumCubes n = (n * (n + 1))^2"
  have "4 * sumCubes (Suc n) = 4 * (sumCubes n + (n+1)^3)"
    by simp
  also have "\<dots> = 4 * sumCubes n + 4*(n+1)^3"
    by simp
  also have "\<dots> = (n*(n+1))^2 + 4*(n+1)^3"
    using IH by simp
  also have "\<dots> = (n+1)^2*(n^2+4*n+4)"
    by algebra
  also have "\<dots> = (n+1)^2*(n+2)^2"
    by algebra
  also have "\<dots> = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "\<dots> = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumCubes (Suc n) = (Suc n * (Suc n + 1))^2"
    by this
qed

(* Proof 2 *)
lemma
  "4 * sumCubes n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumCubes 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume IH : "4 * sumCubes n = (n * (n + 1))^2"
  have "4 * sumCubes (Suc n) = 4 * sumCubes n + 4*(n+1)^3"
    by simp
  also have "\<dots> = (n*(n+1))^2 + 4*(n+1)^3"
    using IH by simp
  also have "\<dots> = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "\<dots> = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumCubes (Suc n) = (Suc n * (Suc n + 1))^2" .
qed

end
