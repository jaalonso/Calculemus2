---
title: Proofs of 0³+1³+2³+3³+···+n³ = (n(n+1)/2)²
date: 2024-09-10 06:00:00 UTC+02:00
category: Induction
has_math: true
---

[mathjax]

Prove that the sum of the first cubes
\\[ 0^3 + 1^3 + 2^3 + 3^3 + ··· + n^3 \\]
is
\\[ \\dfrac{n(n+1)}{2}^2 \\]


To do this, complete the following Lean4 theory:

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

def sumCubes : ℕ → ℕ
  | 0   => 0
  | n+1 => sumCubes n + (n+1)^3

example :
  4 * sumCubes n = (n*(n+1))^2 :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Let
\\[ s(n) = 0^3 + 1^3 + 2^3 + 3^3 + ··· + n^3 \\]
We have to prove that
\\[ s(n) = \\dfrac{n(n+1)}{2}^2 \\]
or, equivalently that
\\[ 4s(n) = (n(n+1))^2 \\]
We will do this by induction on n.

**Base case:** Let \\(n = 0\\). Then,
\\begin{align}
   4s(n) &= 4s(0)        \\\\
         &= 4·0          \\\\
         &= 0            \\\\
         &= (0(0 + 1))^2 \\\\
         &= (n(n + 1))^2
\\end{align}

**Induction step:** Let \\(n = m+1\\) and assume the induction hypothesis (IH)
\\[ 4s(m) = (m(m + 1))^2 \\]
Entonces,
\\begin{align}
   4s(n) &= 4s(m+1)                       \\\\
         &= 4(s(m) + (m+1)^3)             \\\\
         &= 4s(m) + 4(m+1)^3              \\\\
         &= (m(m+1))^2 + 4(m+1)^3         &&\\text{[by IH]} \\\\
         &= (m+1)^2(m^2+4m+4)             \\\\
         &= (m+1)^2(m+2)^2                \\\\
         &= ((m+1)(m+2))^2                \\\\
         &= ((m+1)(m+1+1))^2
\\end{align}

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)

set_option pp.fieldNotation false

@[simp]
def sumCubes : ℕ → ℕ
  | 0   => 0
  | n+1 => sumCubes n + (n+1)^3

-- Proof 1
-- =======

example :
  4 * sumCubes n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumCubes 0 = (0 * (0 + 1)) ^ 2
    calc 4 * sumCubes 0
         = 4 * 0             := by simp only [sumCubes]
       _ = (0 * (0 + 1)) ^ 2 := by simp
  | succ m IH =>
     -- m : ℕ
     -- IH : 4 * sumCubes m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumCubes (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumCubes (m + 1)
         = 4 * (sumCubes m + (m+1)^3)
           := by simp only [sumCubes]
       _ = 4 * sumCubes m + 4*(m+1)^3
           := by ring
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) IH
       _ = (m+1)^2*(m^2+4*m+4)
           := by ring
       _ = (m+1)^2*(m+2)^2
           := by ring
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1))^2
           := by simp

-- Proof 2
-- =======

example :
  4 * sumCubes n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumCubes 0 = (0 * (0 + 1)) ^ 2
    simp
  | succ m IH =>
     -- m : ℕ
     -- IH : 4 * sumCubes m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumCubes (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumCubes (m+1)
         = 4 * sumCubes m + 4*(m+1)^3
           := by {simp ; ring_nf}
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) IH
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1)) ^ 2
           := by simp
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Sum_of_the_first_cubes.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Sum_of_the_first_cubes
imports Main
begin

fun sumCubes :: "nat ⇒ nat" where
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
  also have "… = 4 * sumCubes n + 4*(n+1)^3"
    by simp
  also have "… = (n*(n+1))^2 + 4*(n+1)^3"
    using IH by simp
  also have "… = (n+1)^2*(n^2+4*n+4)"
    by algebra
  also have "… = (n+1)^2*(n+2)^2"
    by algebra
  also have "… = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "… = (Suc n * (Suc n + 1))^2"
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
  also have "… = (n*(n+1))^2 + 4*(n+1)^3"
    using IH by simp
  also have "… = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "… = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumCubes (Suc n) = (Suc n * (Suc n + 1))^2" .
qed

end
</pre>

------------------------------------------------------------------------

**Note:** The code for the previous proofs can be found in the [Calculemus repository](https://github.com/jaalonso/Calculemus2) on GitHub.
