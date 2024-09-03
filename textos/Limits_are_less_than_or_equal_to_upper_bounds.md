---
title: If x is the limit of u and y is an upper bound of u, then x ≤ y
date: 2024-09-03 06:00:00 UTC+02:00
category: Limits
has_math: true
---

[mathjax]

In Lean4, we can define that \\(a\\) is the limit of the sequence \\(u\\) by:
<pre lang="lean">
   def is_limit (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
</pre>
and that \\(a\\) is an upper bound of \\(u\\) by:
<pre lang="lean">
   def is_upper_bound (u : ℕ → ℝ) (a : ℝ) :=
     ∀ n, u n ≤ a
</pre>

Prove that if \\(x\\) is the limit of the sequence \\(u\\) and \\(y\\) is an upper bound of \\(u\\), then \\(x ≤ y\\).

To do this, complete the following Lean4 theory:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  (u : ℕ → ℝ)
variable (x y : ℝ)

def is_limit (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def is_upper_bound (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Let us consider the property from the previous exercise, which states that for all \\(x, y ∈ ℝ\\):
\\[ (∀ ε > 0, y ≤ x + ε) → y ≤ x \\]

To prove \\(x ≤ y\\), it suffices to show that:
\\[ ∀ ε > 0, x ≤ y + ε \\]

Let \\(ε > 0\\). Since \\(x\\) is the limit of the sequence \\(u\\), there exists a \\(k ∈ ℕ\\) such that:
\\[ ∀ n ≥ k, |u(n) - x| < ε \\]
In particular, we have:
\\[ |u(k) - x| < ε \\]
from which it follows that
\\[ -ε < u(k) - x \\]
and rearranging gives us
\\[ x < u(k) + ε \\tag{1} \\]

Since \\(y\\) is an upper bound of \\(u\\), it follows that:
\\[ u(k) < y \\tag{2} \\]

Combining (1) and (2), we obtain
\\[ x < y + ε \\]
which completes the proof.

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable  (u : ℕ → ℝ)
variable (x y : ℝ)

def is_limit (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def is_upper_bound (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

-- Proof 1
-- =======

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  replace hk : -ε < u k - x := neg_lt_of_abs_lt hk
  replace hk : x < u k + ε := neg_lt_sub_iff_lt_add'.mp hk
  apply le_of_lt
  -- ⊢ x < y + ε
  exact lt_add_of_lt_add_right hk (hy k)

-- Proof 2
-- =======

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (le_refl k)
  -- hk : |u k - x| < ε
  apply le_of_lt
  -- ⊢ x < y + ε
  calc x < u k + ε := neg_lt_sub_iff_lt_add'.mp (neg_lt_of_abs_lt hk)
       _ ≤ y + ε   := add_le_add_right (hy k) ε

-- Proof 3
-- =======

example
  (hx : is_limit u x)
  (hy : is_upper_bound u y)
  : x ≤ y :=
by
  apply le_of_forall_pos_le_add
  -- ⊢ ∀ ε > 0, x ≤ y + ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ x ≤ y + ε
  rcases hx ε hε with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - x| < ε
  specialize hk k (by linarith)
  rw [abs_lt] at hk
  -- hk : -ε < u k - x ∧ u k - x < ε
  linarith [hy k]

-- Used lemmas
-- ===========

-- variable (n : ℕ)
-- variable (a b c d : ℝ)
-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (le_of_forall_pos_le_add : (∀ ε > 0, y ≤ x + ε) → y ≤ x)
-- #check (le_of_lt : a < b → a ≤ b)
-- #check (le_refl n : n ≤ n)
-- #check (lt_add_of_lt_add_right : a < b + c → b ≤ d → a < d + c)
-- #check (neg_lt_of_abs_lt : |a| < b → -b < a)
-- #check (neg_lt_sub_iff_lt_add' : -b < a - c ↔ c < a + b)
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limits_are_less_than_or_equal_to_upper_bounds.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Limits_are_less_than_or_equal_to_upper_bounds
imports Main HOL.Real
begin

definition is_limit :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "is_limit u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ < ε)"

definition is_upper_bound :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "is_upper_bound u c ⟷ (∀n. u n ≤ c)"

(* Proof 1 *)
lemma
  fixes x y :: real
  assumes "is_limit u x"
          "is_upper_bound u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) is_limit_def by auto
  then have "¦u k - x¦ < ε"
    by simp
  then have "-ε < u k - x"
    by simp
  then have "x < u k + ε"
    by simp
  moreover have "u k ≤ y"
    using assms(2) is_upper_bound_def by simp
  ultimately show "x ≤ y + ε"
    by simp
qed

(* Proof 2 *)
lemma
  fixes x y :: real
  assumes "is_limit u x"
          "is_upper_bound u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) is_limit_def by auto
  then have "x < u k + ε"
    by auto
  moreover have "u k ≤ y"
    using assms(2) is_upper_bound_def by simp
  ultimately show "x ≤ y + ε"
    by simp
qed

(* Proof 3 *)
lemma
  fixes x y :: real
  assumes "is_limit u x"
          "is_upper_bound u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) is_limit_def by auto
  then show "x ≤ y + ε"
    using assms(2) is_upper_bound_def
    by (smt (verit) order_refl)
qed

end
</pre>

**Note:** The code for the previous demonstrations can be found on [GitHub](https://jaalonso.github.io/calculemus).
