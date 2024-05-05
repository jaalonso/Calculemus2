(* Producto_de_potencias_de_la_misma_base_en_monoides.thy
-- Producto_de_potencias_de_la_misma_base_en_monoides
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponente naturales. En Isabelle/HOL la potencia x^n se
-- caracteriza por los siguientes lemas:
--    power_0   : x ^ 0 = 1
--    power_Suc : x ^ (Suc n) x = x * x ^ n
--
-- Demostrar que
--    x ^ (m + n) = x ^ m * x ^ n
-- ------------------------------------------------------------------ *)

theory Producto_de_potencias_de_la_misma_base_en_monoides
imports Main
begin

context monoid_mult
begin

(* 1\<ordfeminine> demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  have "x ^ (0 + n) = x ^ n"                 by (simp only: add_0)
  also have "\<dots> = 1 * x ^ n"                 by (simp only: mult_1_left)
  also have "\<dots> = x ^ 0 * x ^ n"             by (simp only: power_0)
  finally show "x ^ (0 + n) = x ^ 0 * x ^ n"
    by this
next
  fix m
  assume HI : "x ^ (m + n) = x ^ m * x ^ n"
  have "x ^ (Suc m + n) = x ^ Suc (m + n)"    by (simp only: add_Suc)
  also have "\<dots> = x *  x ^ (m + n)"           by (simp only: power_Suc)
  also have "\<dots> = x *  (x ^ m * x ^ n)"       by (simp only: HI)
  also have "\<dots> = (x *  x ^ m) * x ^ n"       by (simp only: mult_assoc)
  also have "\<dots> = x ^ Suc m * x ^ n"          by (simp only: power_Suc)
  finally show "x ^ (Suc m + n) = x ^ Suc m * x ^ n"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  have "x ^ (0 + n) = x ^ n"                  by simp
  also have "\<dots> = 1 * x ^ n"                  by simp
  also have "\<dots> = x ^ 0 * x ^ n"              by simp
  finally show "x ^ (0 + n) = x ^ 0 * x ^ n"
    by this
next
  fix m
  assume HI : "x ^ (m + n) = x ^ m * x ^ n"
  have "x ^ (Suc m + n) = x ^ Suc (m + n)"    by simp
  also have "\<dots> = x *  x ^ (m + n)"           by simp
  also have "\<dots> = x *  (x ^ m * x ^ n)"       using HI by simp
  also have "\<dots> = (x *  x ^ m) * x ^ n"       by (simp add: mult_assoc)
  also have "\<dots> = x ^ Suc m * x ^ n"          by simp
  finally show "x ^ (Suc m + n) = x ^ Suc m * x ^ n"
    by this
qed

(* 3\<ordfeminine> demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  then show ?case
    by (simp add: algebra_simps)
qed

(* 4\<ordfeminine> demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
  by (induct m) (simp_all add: algebra_simps)

(* 5\<ordfeminine> demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
  by (simp only: power_add)

end

end
