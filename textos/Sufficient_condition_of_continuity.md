---
title: If f is continuous at a and the limit of u(n) is a, then the limit of f(u(n)) is f(a)
date: 2024-09-04 06:00:00 UTC+02:00
category: Limits
has_math: true
---

[mathjax]

In Lean4, we can define that \\(a\\) is the limit of the sequence \\(u\\) by:
<pre lang="haskell">
   def is_limit (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
</pre>
and that \\(f\\) is continuous at \\(a\\) by:
<pre lang="haskell">
   def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε
</pre>

To prove that if the function \\(f\\) is continuous at the point \\(a\\), and the sequence \\(u(n)\\) converges to \\(a\\), then the sequence \\(f(u(n))\\) converges to \\(f(a)\\).

To do this, complete the following Lean4 theory:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

def is_limit (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

Let \\(ε > 0\\). We need to prove that there exists a \\(k ∈ ℕ\\) such that for all \\(n ≥ k\\),
\\[ |(f ∘ u)(n) - f(a)| ≤ ε \\tag{1} \\]

Since \\(f\\) is continuous at \\(a\\), there exists a \\(δ > 0\\) such that
\\[ |x - a| ≤ δ → |f(x) - f(a)| ≤ ε \\tag{2} \\]
Furthermore, because the limit of \\(u(n)\\) is \\(a\\), there exists a \\(k ∈ ℕ\\) such that for all \\(n ≥ k\\),
\\[ |u(n) - a| ≤ δ \\tag{3} \\]

To prove (1), let \\(n ∈ ℕ\\) such that \\(n ≥ k\\). Then,
\\begin{align}
  |(f ∘ u)(n) - f(a)| &= |f(u(n)) - f(a)|            \\\\
                      &≤ ε                           &&\\text{[by (2) and (3)]}
\\end{align}

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

def is_limit (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

-- Proof 1
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  obtain ⟨k, hk⟩ := hu δ hδ1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  use k
  -- ⊢ ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(f ∘ u) n - f a| ≤ ε
  calc |(f ∘ u) n - f a| = |f (u n) - f a| := by simp only [Function.comp_apply]
                       _ ≤ ε               := hδ2 (u n) (hk n hn)

-- Proof 2
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  obtain ⟨k, hk⟩ := hu δ hδ1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  exact ⟨k, fun n hn ↦ hδ2 (u n) (hk n hn)⟩

-- Proof 3
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hu δ hδ1 with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  use k
  -- ⊢ ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(f ∘ u) n - f a| ≤ ε
  apply hδ2
  -- ⊢ |u n - a| ≤ δ
  exact hk n hn

-- Proof 4
-- =======

example
  (hf : continuous_at f a)
  (hu : is_limit u a)
  : is_limit (f ∘ u) (f a) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(f ∘ u) n - f a| ≤ ε
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩
  -- δ : ℝ
  -- hδ1 : δ > 0
  -- hδ2 : ∀ (x : ℝ), |x - a| ≤ δ → |f x - f a| ≤ ε
  rcases hu δ hδ1 with ⟨k, hk⟩
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| ≤ δ
  exact ⟨k, fun n hn ↦ hδ2 (u n) (hk n hn)⟩

-- Used lemmas
-- ===========

-- variable (g : ℝ → ℝ)
-- variable (x : ℝ)
-- #check (Function.comp_apply : (g ∘ f) x = g (f x))
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Sufficient_condition_of_continuity.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Sufficient_condition_of_continuity
imports Main HOL.Real
begin

definition is_limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "is_limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

definition continuous_at :: "(real ⇒ real) ⇒ real ⇒ bool" where
  "continuous_at f a ⟷
   (∀ε>0. ∃δ>0. ∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"

(* Proof 1 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f ∘ u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continuous_at_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) is_limite_def hδ1 by auto
  have "∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
  proof (intro allI impI)
    fix n
    assume "n ≥ k"
    then have "¦u n - a¦ ≤ δ"
      using hk by auto
    then show "¦(f ∘ u) n - f a¦ ≤ ε"
      using hδ2 by simp
  qed
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    by auto
qed

(* Proof 2 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f ∘ u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continuous_at_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) is_limite_def hδ1 by auto
  have "∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hk hδ2 by simp
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    by auto
qed

(* Proof 3 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f ∘ u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continuous_at_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) is_limite_def hδ1 by auto
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hk hδ2 by auto
qed

(* Proof 4 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f ∘ u) (f a)"
proof (unfold is_limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where
              hδ : "δ > 0 ∧ (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continuous_at_def by auto
  then obtain k where "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) is_limite_def by auto
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hδ by auto
qed

(* Proof 5 *)
lemma
  assumes "continuous_at f a"
          "is_limite u a"
  shows "is_limite (f ∘ u) (f a)"
  using assms continuous_at_def is_limite_def
  by force

end
</pre>

**Note:** The demonstrations using Lean 4 can be found in the [src](https://github.com/jaalonso/Calculemus2/tree/main/src) directory of [the Calculemus repository](https://github.com/jaalonso/Calculemus2/tree/main/thy) on GitHub, and the demonstrations using Isabelle/HOL can be found in the [thy](https://github.com/jaalonso/Calculemus2) directory.
