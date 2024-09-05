---
title: Proofs of "0 + 1 + 2 + 3 + ··· + n = n × (n + 1)/2"
date: 2024-09-05 06:00:00 UTC+02:00
category: Induction
has_math: true
---

[mathjax]

Prove that the sum of the natural numbers
\\[ 0 + 1 + 2 + 3 + ··· + n \\]
is \\(\\dfrac{n(n + 1)}{2}\\) \\]

To do this, complete the following Lean4 theory:

<pre lang="lean">
import Init.Data.Nat.Basic
import Mathlib.Tactic

open Nat

variable (n : Nat)

set_option pp.fieldNotation false

def sum : Nat → Nat
  | 0      => 0
  | succ n => sum n + (n+1)

example :
  2 * sum n = n * (n + 1) :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Let
\\[ s(n) = 0 + 1 + 2 + 3 + ··· + n \\]
We need to prove that
\\[ s(n) = \\defrac{n(n + 1)}{2} \\]
or, equivalently, that
\\[ 2s(n) = n(n + 1) \\]
We will do this by induction on \\(n\\).

**Base Case:** Let \\(n = 0\\). Then,
\\begin{align}
   2s(n) &= 2s(0)     \\\\
         &= 2·0       \\\\
         &= 0         \\\\
         &= 0.(0 + 1) \\\\
         &= n.(n + 1)
\\end{align}

**Induction Step:** Let \\(n = m + 1\\) and assume the induction hypothesis (IH)
\\[ 2s(m) = m \\
Then,
\\begin{align}
   2s(n) &= 2s(m+1)                \\\\
         &= 2(s(m) + (m+1))        \\\\
         &= 2s(m) + 2(m+1)         \\\\
         &= m(m + 1) + 2(m + 1)    &&\\text{[by IH]} \\\\
         &= (m + 2)(m + 1)         \\\\
         &= (m + 1)(m + 2)         \\\\
         &= n(n+1)
\\end{align}

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Init.Data.Nat.Basic
import Mathlib.Tactic

open Nat

variable (n : Nat)

set_option pp.fieldNotation false

def sum : Nat → Nat
  | 0      => 0
  | succ n => sum n + (n+1)

@[simp]
lemma sum_zero : sum 0 = 0 := rfl

@[simp]
lemma sum_succ : sum (n + 1) = sum n + (n+1) := rfl

-- Proof 1
-- =======

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    calc 2 * sum 0
         = 2 * 0       := congrArg (2 * .) sum_zero
       _ = 0           := mul_zero 2
       _ = 0 * (0 + 1) := zero_mul (0 + 1)
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := congrArg (2 * .) (sum_succ n)
       _ = 2 * sum n + 2 * (n + 1)  := mul_add 2 (sum n) (n + 1)
       _ = n * (n + 1) + 2 * (n + 1) := congrArg (. + 2 * (n + 1)) HI
       _ = (n + 2) * (n + 1)         := (add_mul n 2 (n + 1)).symm
       _ = (n + 1) * (n + 2)         := mul_comm (n + 2) (n + 1)

-- Proof 2
-- =======

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    calc 2 * sum 0
         = 2 * 0       := rfl
       _ = 0           := rfl
       _ = 0 * (0 + 1) := rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := rfl
       _ = 2 * sum n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 2) * (n + 1)         := by ring
       _ = (n + 1) * (n + 2)         := by ring

-- Proof 3
-- =======

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sum 0 = 0 * (0 + 1)
    rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * sum n = n * (n + 1)
    -- ⊢ 2 * sum (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * sum (n + 1)
         = 2 * (sum n + (n + 1))    := rfl
       _ = 2 * sum n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 1) * (n + 2)         := by ring

-- Proof 4
-- =======

example :
  2 * sum n = n * (n + 1) :=
by
  induction n with
  | zero => rfl
  | succ n HI => unfold sum ; linarith [HI]

-- Used lemmas
-- ===========

-- variable (a b c : ℕ)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_zero a : a * 0 = 0)
-- #check (zero_mul a : 0 * a = 0)
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Sum_of_the_first_n_natural_numbers.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Sum_of_the_first_n_natural_numbers
imports Main
begin

fun sum :: "nat ⇒ nat" where
  "sum 0       = 0"
| "sum (Suc n) = sum n + Suc n"

(* Proof 1 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  have "2 * sum 0 = 2 * 0"
    by (simp only: sum.simps(1))
  also have "… = 0"
    by (rule mult_0_right)
  also have "… = 0 * (0 + 1)"
    by (rule mult_0 [symmetric])
  finally show "2 * sum 0 = 0 * (0 + 1)"
    by this
next
  fix n
  assume HI : "2 * sum n = n * (n + 1)"
  have "2 * sum (Suc n) = 2 * (sum n + Suc n)"
    by (simp only: sum.simps(2))
  also have "… = 2 * sum n + 2 * Suc n"
    by (rule add_mult_distrib2)
  also have "… = n * (n + 1) + 2 * Suc n"
    by (simp only: HI)
  also have "… = n * (n + Suc 0) + 2 * Suc n"
    by (simp only: One_nat_def)
  also have "… = n * Suc (n + 0) + 2 * Suc n"
    by (simp only: add_Suc_right)
  also have "… = n * Suc n + 2 * Suc n"
    by (simp only: add_0_right)
  also have "… = (n + 2) * Suc n"
    by (simp only: add_mult_distrib)
  also have "… = Suc (Suc n) * Suc n"
    by (simp only: add_2_eq_Suc')
  also have "… = (Suc n + 1) * Suc n"
    by (simp only: Suc_eq_plus1)
  also have "… = Suc n * (Suc n + 1)"
    by (simp only: mult.commute)
  finally show "2 * sum (Suc n) = Suc n * (Suc n + 1)"
    by this
qed

(* Proof 2 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  have "2 * sum 0 = 2 * 0" by simp
  also have "… = 0" by simp
  also have "… = 0 * (0 + 1)" by simp
  finally show "2 * sum 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * sum n = n * (n + 1)"
  have "2 * sum (Suc n) = 2 * (sum n + Suc n)" by simp
  also have "… = 2 * sum n + 2 * Suc n" by simp
  also have "… = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "… = n * (n + Suc 0) + 2 * Suc n" by simp
  also have "… = n * Suc (n + 0) + 2 * Suc n" by simp
  also have "… = n * Suc n + 2 * Suc n" by simp
  also have "… = (n + 2) * Suc n" by simp
  also have "… = Suc (Suc n) * Suc n" by simp
  also have "… = (Suc n + 1) * Suc n" by simp
  also have "… = Suc n * (Suc n + 1)" by simp
  finally show "2 * sum (Suc n) = Suc n * (Suc n + 1)" .
qed

(* Proof 3 *)
lemma
  "2 * sum n = n * (n + 1)"
proof (induct n)
  have "2 * sum 0 = 2 * 0" by simp
  also have "… = 0" by simp
  also have "… = 0 * (0 + 1)" by simp
  finally show "2 * sum 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * sum n = n * (n + 1)"
  have "2 * sum (Suc n) = 2 * (sum n + Suc n)" by simp
  also have "… = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "… = (n + 2) * Suc n" by simp
  also have "… = Suc n * (Suc n + 1)" by simp
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
</pre>

**Note:** The demonstrations using Lean 4 can be found in the [src](https://github.com/jaalonso/Calculemus2/tree/main/src) directory of [the Calculemus repository](https://github.com/jaalonso/Calculemus2/tree/main/thy) on GitHub, and the demonstrations using Isabelle/HOL can be found in the [thy](https://github.com/jaalonso/Calculemus2) directory.
