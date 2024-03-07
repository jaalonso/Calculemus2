(* Interseccion_de_los_primos_y_los_mayores_que_dos.thy
   Los primos mayores que 2 son impares.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 6-marzo-2024
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
  Los números primos, los mayores que 2 y los impares se definen por
     def primos      = {n \<in> \<nat> . prime n}
     def mayoresQue2 = {n \<in> \<nat> . n > 2}
     def impares     = {n \<in> \<nat> . \<not> even n}

  Demostrar que
     primos \<inter> mayoresQue2 \<subseteq> impares
  ------------------------------------------------------------------- *)

theory Interseccion_de_los_primos_y_los_mayores_que_dos
imports Main "HOL-Number_Theory.Number_Theory"
begin

definition primos :: "nat set" where
  "primos = {n \<in> \<nat> . prime n}"

definition mayoresQue2 :: "nat set" where
  "mayoresQue2 = {n \<in> \<nat> . n > 2}"

definition impares :: "nat set" where
  "impares = {n \<in> \<nat> . \<not> even n}"

(* 1\<ordfeminine> demostración *)
lemma "primos \<inter> mayoresQue2 \<subseteq> impares"
proof
  fix x
  assume "x \<in> primos \<inter> mayoresQue2"
  then have "x \<in> \<nat> \<and> prime x \<and> 2 < x"
    by (simp add: primos_def mayoresQue2_def)
  then have "x \<in> \<nat> \<and> odd x"
    by (simp add: prime_odd_nat)
  then show "x \<in> impares"
    by (simp add: impares_def)
qed

(* 2\<ordfeminine> demostración *)
lemma "primos \<inter> mayoresQue2 \<subseteq> impares"
  unfolding primos_def mayoresQue2_def impares_def
  by (simp add: Collect_mono_iff Int_def prime_odd_nat)

(* 3\<ordfeminine> demostración *)
lemma "primos \<inter> mayoresQue2 \<subseteq> impares"
  unfolding primos_def mayoresQue2_def impares_def
  by (auto simp add: prime_odd_nat)

end
