---
title: Proofs of a+(a+d)+(a+2d)+···+(a+nd)=(n+1)(2a+nd)/2
date: 2024-09-07 06:00:00 UTC+02:00
category: Induction
has_math: true
---

[mathjax]

Prove that the sum of the terms of the arithmetic progression
\\[ a + (a + d) + (a + 2d) + ··· + (a + nd) \\]
is
\\[ \\dfrac{(n + 1)(2a + nd)}{2} \\]

To do this, complete the following Lean4 theory:

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a d : ℝ)

def sumAP : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, d, n + 1 => sumAP a d n + (a + (n + 1) * d)

example :
  2 * sumAP a d n = (n + 1) * (2 * a + n * d) :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Let
\\[ s(a,d,n) = a + (a + d) + (a + 2d) + ··· + (a + nd) \\]
We need to prove that
\\[ s(a,d,n) = \\dfrac{(n + 1)(2a + nd)}{2} \\]
or, equivalently that
\\[ 2s(a,d,n) = (n + 1)(2a + nd) \\]
We will do this by induction on \\(n\\).

**Base case:** Let \\(n = 0\\). Then,
\\begin{align}
   2s(a,d,n) &= 2s(a,d,0)         \\\\
             &= 2a                \\\\
             &= (0 + 1)(2a + 0.d) \\\\
             &= (n + 1)(2a + nd)
\\end{align}

**Induction step:** Let \\(n = m+1\\) and assume the induction hypothesis (IH)
\\[ 2s(m) = (m + 1)(2a + md) \\]
Then,
\\begin{align}
   2s(n) &= 2s(m+1)                              \\\\
         &= 2(s(a,d,m) + (a + (m + 1)d))         \\\\
         &= 2s(a,d,m) + 2(a + (m + 1)d)          \\\\
         &= ((m + 1)(2a + md)) + 2(a + (m + 1)d) &&\\text{[by IH]} \\\\
         &= (m + 2)(2a + (m + 1)d)               \\\\
         &= (n + 1)(2a + nd)
\\end{align}

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a d : ℝ)

set_option pp.fieldNotation false

def sumAP : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, d, n + 1 => sumAP a d n + (a + (n + 1) * d)

@[simp]
lemma sumAP_zero :
  sumAP a d 0 = a :=
by simp only [sumAP]

@[simp]
lemma sumAP_succ :
  sumAP a d (n + 1) = sumAP a d n + (a + (n + 1) * d) :=
by simp only [sumAP]

-- Proof 1
-- =======

example :
  2 * sumAP a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumAP a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    have h : 2 * sumAP a d 0 = (0 + 1) * (2 * a + 0 * d) :=
      calc 2 * sumAP a d 0
           = 2 * a
               := congrArg (2 * .) (sumAP_zero a d)
         _ = (0 + 1) * (2 * a + 0 * d)
               := by ring_nf
    exact_mod_cast h
  | succ m IH =>
    -- m : ℕ
    -- IH : 2 * sumAP a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumAP a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumAP a d (succ m)
         = 2 * (sumAP a d m + (a + (m + 1) * d))
           := congrArg (2 * .) (sumAP_succ m a d)
       _ = 2 * sumAP a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) IH
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast

-- Proof 2
-- =======

example :
  2 * sumAP a d n = (n + 1) * (2 * a + n * d) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * sumAP a d 0 = (↑0 + 1) * (2 * a + ↑0 * d)
    simp
  | succ m IH =>
    -- m : ℕ
    -- IH : 2 * sumAP a d m = (↑m + 1) * (2 * a + ↑m * d)
    -- ⊢ 2 * sumAP a d (m + 1) = (↑(m + 1) + 1) * (2 * a + ↑(m + 1) * d)
    calc 2 * sumAP a d (succ m)
         = 2 * (sumAP a d m + (a + (m + 1) * d))
           := rfl
       _ = 2 * sumAP a d m + 2 * (a + (m + 1) * d)
           := by ring_nf
       _ = ((m + 1) * (2 * a + m * d)) + 2 * (a + (m + 1) * d)
           := congrArg (. + 2 * (a + (m + 1) * d)) IH
       _ = (m + 2) * (2 * a + (m + 1) * d)
           := by ring_nf
       _ = (succ m + 1) * (2 * a + succ m * d)
           := by norm_cast
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Sum_of_arithmetic_progression.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Sum_of_arithmetic_progression
imports Main HOL.Real
begin

fun sumAP :: "real ⇒ real ⇒ nat ⇒ real" where
  "sumAP a d 0 = a"
| "sumAP a d (Suc n) = sumAP a d n + (a + (n + 1) * d)"

(* Proof 1 *)
lemma
  "2 * sumAP a d n = (n + 1) * (2 * a + n * d)"
proof (induct n)
  show "2 * sumAP a d 0 =
        (real 0 + 1) * (2 * a + real 0 * d)"
    by simp
next
  fix n
  assume IH : "2 * sumAP a d n =
               (n + 1) * (2 * a + n * d)"
  have "2 * sumAP a d (Suc n) =
        2 * (sumAP a d n + (a + (n + 1) * d))"
    by simp
  also have "… = 2 * sumAP a d n + 2 * (a + (n + 1) * d)"
    by simp
  also have "… = (n + 1) * (2 * a + n * d) + 2 * (a + (n + 1) * d)"
    using IH by simp
  also have "… = (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by (simp add: algebra_simps)
  finally show "2 * sumAP a d (Suc n) =
                (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by this
qed

(* Proof 2 *)
lemma
  "2 * sumAP a d n = (n + 1) * (2*a + n*d)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: algebra_simps)
qed

(* Proof 3 *)
lemma
  "2 * sumAP a d n = (n + 1) * (2*a + n*d)"
by (induct n) (simp_all add: algebra_simps)

end
</pre>

------------------------------------------------------------------------

**Note:** The code for the previous proofs can be found in the [Calculemus repository](https://github.com/jaalonso/Calculemus2) on GitHub.
