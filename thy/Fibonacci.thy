(* Fibonacci.thy
-- Equivalence of definitions of the Fibonacci function.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, August 29, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- In Isabelle/HOL, the Fibonacci function can be defined as
--   fun fibonacci :: "nat \<Rightarrow> nat"
--     where
--       "fibonacci 0 = 0"
--     | "fibonacci (Suc 0) = 1"
--     | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"
--
-- Another definition is
--   fun fibAux :: "nat => nat × nat"
--     where
--        "fibAux 0 = (0, 1)"
--      | "fibAux (Suc n) = (let (a, b) = fibAux n in (b, a + b))"
--
--   definition fib :: "nat \<Rightarrow> nat" where
--     "fib n = (fst (fibAux n))"
--
-- Prove that both definitions are equivalent; that is,
--    fibonacci n = fib n
-- ------------------------------------------------------------------ *)

theory Fibonacci
imports Main
begin

fun fibonacci :: "nat ⇒ nat"
  where
    "fibonacci 0 = 0"
  | "fibonacci (Suc 0) = 1"
  | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

fun fibAux :: "nat => nat × nat"
  where
     "fibAux 0 = (0, 1)"
   | "fibAux (Suc n) = (let (a, b) = fibAux n in (b, a + b))"

definition fib :: "nat ⇒ nat" where
  "fib n = fst (fibAux n)"

lemma fib_suma :
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"
proof (induct n)
  show "fib (Suc (Suc 0)) = fib 0 + fib (Suc 0)"
    by (simp add: fib_def)
next
  fix n
  assume IH : "fib (Suc (Suc n)) = fib n + fib (Suc n)"
  have "fib (Suc (Suc (Suc n))) = fst (fibAux (Suc (Suc (Suc n))))"
    by (simp add: fib_def)
  also have "… = snd (fibAux (Suc (Suc n)))"
    by (simp add: prod.case_eq_if)
  also have "… = fst (fibAux (Suc n)) + snd (fibAux (Suc n))"
    by (metis fibAux.simps(2) snd_conv split_def)
  also have "… = fib (Suc n) + snd (fibAux (Suc n))"
    using fib_def by auto
  also have "… = fib (Suc n) + fib (Suc (Suc n))"
    by (simp add: fib_def prod.case_eq_if)
  finally show "fib (Suc (Suc (Suc n))) = fib (Suc n) + fib (Suc (Suc n))"
    by this
qed

lemma "fibonacci n = fib n"
proof (induct n rule: fibonacci.induct)
  show "fibonacci 0 = fib 0"
    by (simp add: fib_def)
next
  show "fibonacci (Suc 0) = fib (Suc 0)"
    by (simp add: fib_def)
next
  fix n
  assume IH1 : "fibonacci n = fib n"
  assume IH2 : "fibonacci (Suc n) = fib (Suc n)"
  have "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"
    by simp
  also have "… = fib n + fib (Suc n)"
    by (simp add: IH1 IH2)
  also have "… = fib (Suc (Suc n))"
    by (simp add: fib_suma)
  finally show "fibonacci (Suc (Suc n)) = fib (Suc (Suc n))"
    by this
qed

end
