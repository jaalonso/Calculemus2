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
--   fun fibAux :: "nat => nat \<times> nat"
--     where
--        "fibAux 0 = (0, 1)"
--     | "fibAux (Suc n) = (snd (fibAux n), fst (fibAux n) + snd (fibAux n))"
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

fun fibonacci :: "nat \<Rightarrow> nat"
  where
    "fibonacci 0 = 0"
  | "fibonacci (Suc 0) = 1"
  | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

fun fibAux :: "nat => nat \<times> nat"
  where
     "fibAux 0 = (0, 1)"
   | "fibAux (Suc n) = (snd (fibAux n), fst (fibAux n) + snd (fibAux n))"

definition fib :: "nat \<Rightarrow> nat" where
  "fib n = (fst (fibAux n))"

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
  also have "\<dots> = fib n + fib (Suc n)"
    by (simp add: IH1 IH2)
  also have "\<dots> = fib (Suc (Suc n))"
    by (simp add: fib_def)
  finally show "fibonacci (Suc (Suc n)) = fib (Suc (Suc n))"
    by this
qed

end
