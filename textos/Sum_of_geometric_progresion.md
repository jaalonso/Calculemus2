---
title: Proofs of a+aq+aq²+···+aqⁿ = a(1-qⁿ⁺¹)/(1-q)
date: 2024-09-09 06:00:00 UTC+02:00
category: Induction
has_math: true
---

[mathjax]

Prove that if \\(q ≠ 1\\), then the sum of the terms of the geometric progression
\\[ a + aq + aq^2 + ··· + aq^n \\]
is
\\[ \\dfrac{a(1 - q^{n+1})}{1 - q} \\]

To do this, complete the following Lean4 theory:

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a q : ℝ)

def sumGP : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, q, n + 1 => sumGP a q n + (a * q^(n + 1))

example
  (h : q ≠ 1)
  : sumGP a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Let
\\[ s(a,q,n) = a + aq + aq^2 + ··· + aq^n \\]
We must show that
\\[ s(a,q,n) = \\dfrac{a(1 - q^{n+1}}{1 - q} \\]
or, equivalently, that
\\[ (1 - q)s(a,q,n) = a(1 - q^{n+1})
We will proceed by induction on \\(n\\).

**Base case:** Let \\(n = 0\\). Then,
\\begin{align}
   (1 - q)s(a,q,n) &= (1 - q)s(a, q, 0) \\\\
                   &= (1 - q)a          \\\\
                   &= a(1 - q^{0 + 1})  \\\\
                   &= a(1 - q^{n + 1})
\\end{align}

**Induction step:** Let \\(n = m+1\\) and assume the induction hypothesis (IH)
\\[ (1 - q)s(a,q,m) = a(1 - q^{m + 1}) \\]
Then
\\begin{align}
   (1 - q)s(a,q,n)                           \\\\
   &= (1 - q)s(a,q,m+1)                      \\\\
   &= (1 - q)(s(a,q,m) + aq^(m + 1))         \\\\
   &= (1 - q)s(a,q,m) + (1 - q)aq^(m + 1)    \\\\
   &= a(1 - q^(m + 1)) + (1 - q)aq^(m + 1)   &&\\text{[by IH]} \\\\
   &= a(1 - q^(m + 1 + 1))                   \\\\
   &= a(1 - q^(n + 1))
\\end{align}

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a q : ℝ)

set_option pp.fieldNotation false

@[simp]
def sumGP : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, q, n + 1 => sumGP a q n + (a * q^(n + 1))

-- Proof 1
-- =======

example
  (h : q ≠ 1)
  : sumGP a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))
    calc (1 - q) * sumGP a q 0
         = (1 - q) * a           := by simp only [sumGP]
       _ = a * (1 - q)           := by simp only [mul_comm]
       _ = a * (1 - q ^ 1)       := by simp
       _ = a * (1 - q ^ (0 + 1)) := by simp
  | succ m IH =>
    -- m : ℕ
    -- IH : (1 - q) * sumGP a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumGP a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumGP a q (m + 1)
         = (1 - q) * (sumGP a q m + (a * q^(m + 1)))
           := by simp only [sumGP]
       _ = (1 - q) * sumGP a q m + (1 - q) * (a * q ^ (m + 1))
           := by rw [left_distrib]
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) IH
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf

-- Proof 2
-- =======

example
  (h : q ≠ 1)
  : sumGP a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))
    simp
    -- ⊢ (1 - q) * a = a * (1 - q)
    ring_nf
  | succ m IH =>
    -- m : ℕ
    -- IH : (1 - q) * sumGP a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumGP a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumGP a q (m + 1)
         = (1 - q) * (sumGP a q m + (a * q ^ (m + 1)))
           := rfl
       _ = (1 - q) * sumGP a q m + (1 - q) * (a * q ^ (m + 1))
           := by ring_nf
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) IH
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Sum_of_geometric_progresion.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Sum_of_geometric_progresion
imports Main HOL.Real
begin

fun sumGP :: "real ⇒ real ⇒ nat ⇒ real" where
  "sumGP a q 0 = a"
| "sumGP a q (Suc n) = sumGP a q n + (a * q^(n + 1))"

(* Proof 1 *)
lemma
  "(1 - q) * sumGP a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume IH : "(1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumGP a q (Suc n) =
        (1 - q) * (sumGP a q n + (a * q^(n + 1)))"
    by simp
  also have "… = (1 - q) * sumGP a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using IH by simp
  also have "… = a * (1 - q ^ (n + 1) + (1 - q) * q^(n + 1))"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q^(n + 2))"
    by simp
  also have "… = a * (1 - q ^ (Suc n + 1))"
    by simp
  finally show "(1 - q) * sumGP a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by this
qed

(* Proof 2 *)
lemma
  "(1 - q) * sumGP a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume IH : "(1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumGP a q (Suc n) =
        (1 - q) * sumGP a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using IH by simp
  also have "… = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  finally show "(1 - q) * sumGP a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by simp
qed

(* Proof 3 *)
lemma
  "(1 - q) * sumGP a q n = a * (1 - q^(n + 1))"
  using power_add
  by (induct n) (auto simp: algebra_simps)

end
</pre>

------------------------------------------------------------------------

**Note:** The code for the previous proofs can be found in the [Calculemus repository](https://github.com/jaalonso/Calculemus2) on GitHub.
