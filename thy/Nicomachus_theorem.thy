(* Nicomachus_theorem.lean
   Nicomachus’s theorem.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Seville, January 3, 2025
   ================================================================== *)

(* ---------------------------------------------------------------------
   Prove the [Nicomachus's theorem](https://tinyurl.com/gvamrds) which
   states that the sum of the cubes of the first n natural numbers is
   equal to the square of the sum of the first n natural numbers; that
   is, for any natural number n we have
      1³ + 2³ + ... + n³ = (1 + 2 + ... + n)²
   ------------------------------------------------------------------- *)

theory Nicomachus_theorem
imports Main
begin

(* (sum n) is the sum of the first n natural numbers. *)
fun sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0"
| "sum (Suc n) = sum n + Suc n"

(* (sumCubes n) is the sum of the cubes of the first n natural numbers. *)
fun sumCubes :: "nat \<Rightarrow> nat" where
  "sumCubes 0 = 0"
| "sumCubes (Suc n) = sumCubes n + (Suc n)^3"

(* Lemma 1: 2(1 + 2 + ... + n) = n(n+1) *)

(* Proof 1 of Lemma 1 *)
lemma "2 * sum n = n^2 + n"
proof (induct n)
  show "2 * sum 0 = 0^2 + 0" by simp
next
  fix n
  assume "2 * sum n = n^2 + n"
  then have "2 * sum (Suc n) = n^2 + n + 2 + 2 * n"
    by simp
  also have "\<dots> = (Suc n)^2 + Suc n"
    by (simp add: power2_eq_square)
  finally show "2 * sum (Suc n) = (Suc n)^2 + Suc n"
    by this
qed

(* Proof 2 of Lemma 1 *)
lemma sum_formula:
  "2 * sum n = n^2 + n"
  by (induct n) (auto simp add: power2_eq_square)

(* Lemma 2: 4(1³ + 2³ + ... + n³) = (n(n+1))² *)

(* Proof 1 of Lemma 2 *)
lemma "4 * sumCubes n = (n^2 + n)^2"
proof (induct n)
  show "4 * sumCubes 0 = (0^2 + 0)^2"
    by simp
next
  fix n
  assume "4 * sumCubes n = (n^2 + n)^2"
  then have "4 * sumCubes (Suc n) = (n^2 + n)^2 + 4 * (Suc n)^3"
    by simp
  then show "4 * sumCubes (Suc n) = ((Suc n)^2 + Suc n)^2"
  by (simp add: algebra_simps
                power2_eq_square
                power3_eq_cube )
qed

(* Proof 2 of Lemma 2 *)
lemma sumCubes_formula:
  "4 * sumCubes n = (n^2 + n)^2"
  by (induct n) (auto simp add: algebra_simps
                                power2_eq_square
                                power3_eq_cube)

(* Auxiliary lemma *)
lemma aux: "4 * (m::nat) = (2 * n)^2 \<Longrightarrow> m = n^2"
  by (simp add: power2_eq_square)

(* Nicomachus’s theorem. *)
theorem  Nicomachus :
  "sumCubes n = (sum n)^2"
  by (simp only: sum_formula sumCubes_formula aux)

end
