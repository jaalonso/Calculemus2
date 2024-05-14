(* Potencias_de_potencias_en_monoides.thy
-- Si M es un monoide, a \<in> M y m, n \<in> \<nat>, entonces a^(m\<sqdot>n) = (a^m)^n
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponentes naturales. En Lean4, la potencia x^n se
-- se caracteriza por los siguientes lemas:
--    power_0   : x ^ 0 = 1
--    power_Suc : x ^ (Suc n) x = x * x ^ n
--
-- Demostrar que si M es un monoide, a \<in> M y m, n \<in> \<nat>, entonces
--    a^(m * n) = (a^m)^n
--
-- Indicación: Se puede usar el lema
--    power_add : a^(m + n) = a^m * a^n
-- ------------------------------------------------------------------ *)

theory Potencias_de_potencias_en_monoides
imports Main
begin

context monoid_mult
begin

(* 1\<ordfeminine> demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  have "a ^ (m * 0) = a ^ 0"
    by (simp only: mult_0_right)
  also have "\<dots> = 1"
    by (simp only: power_0)
  also have "\<dots> = (a ^ m) ^ 0"
    by (simp only: power_0)
  finally show "a ^ (m * 0) = (a ^ m) ^ 0"
    by this
next
  fix n
  assume HI : "a ^ (m * n) = (a ^ m) ^ n"
  have "a ^ (m * Suc n) = a ^ (m + m * n)"
    by (simp only: mult_Suc_right)
  also have "\<dots> = a ^ m * a ^ (m * n)"
    by (simp only: power_add)
  also have "\<dots> = a ^ m * (a ^ m) ^ n"
    by (simp only: HI)
  also have "\<dots> = (a ^ m) ^ Suc n"
    by (simp only: power_Suc)
  finally show "a ^ (m * Suc n) = (a ^ m) ^ Suc n"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  have "a ^ (m * 0) = a ^ 0"               by simp
  also have "\<dots> = 1"                       by simp
  also have "\<dots> = (a ^ m) ^ 0"             by simp
  finally show "a ^ (m * 0) = (a ^ m) ^ 0" .
next
  fix n
  assume HI : "a ^ (m * n) = (a ^ m) ^ n"
  have "a ^ (m * Suc n) = a ^ (m + m * n)" by simp
  also have "\<dots> = a ^ m * a ^ (m * n)"     by (simp add: power_add)
  also have "\<dots> = a ^ m * (a ^ m) ^ n"     using HI by simp
  also have "\<dots> = (a ^ m) ^ Suc n"         by simp
  finally show "a ^ (m * Suc n) =
                (a ^ m) ^ Suc n"           .
qed

(* 3\<ordfeminine> demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: power_add)
qed

(* 4\<ordfeminine> demostración *)

lemma  "a^(m * n) = (a^m)^n"
  by (induct n) (simp_all add: power_add)

(* 5\<ordfeminine> demostración *)

lemma "a^(m * n) = (a^m)^n"
  by (simp only: power_mult)

end

end
