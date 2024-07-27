---
title: Si u es una sucesión no decreciente y su límite es a, entonces u(n) ≤ a para todo n
date: 2024-07-27 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, una sucesión \\(u_0, u_1, u_2, ...\\) se puede representar mediante una función \\(u : ℕ → ℝ\\) de forma que \\(u(n)\\) es \\(u_n\\).

En Lean4, se define que \\(a\\) es el límite de la sucesión \\(u\\), por
<pre lang="lean">
   def limite (u: ℕ → ℝ) (a: ℝ) :=
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>
y que la sucesión \\(u\\) es no decreciente por
<pre lang="lean">
   def no_decreciente (u : ℕ → ℝ) :=
     ∀ n m, n ≤ m → u n ≤ u m
</pre>

Demostrar con Lean4 que si \\(u\\) es una sucesión no decreciente y su límite es \\(a\\), entonces \\(u(n) ≤ a\\) para todo \\(n\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {u : ℕ → ℝ}
variable (a : ℝ)

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def no_decreciente (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Lo demostraremos por reducción al absurdo. Para ello, sea \\(n ∈ ℕ\\) tal que
\\[ a < u(n) \\]
Entonces,
\\[ u(n) - a > 0 \\]
y, puesto que \\(a\\) es límite de \\(u\\), existe un \\(m ∈ ℕ\\) tal que
\\[ (∀ n' ≥ m)[|u(n') - a| < u(n) - a] \\tag{1} \\]
Sea \\(k = \\max(n, m)\\). Entonces,
\\begin{align}
   k &≥ n \\tag{2} \\\\
   k &≥ m \\tag{3}
\\end{align}
Por (1) y (3) se tiene que
\\[ |u(k) - a| < u(n) - a \\tag{4} \\]
Por (2), puesto que \\(u\\) es no decreciente, se tiene que
\\[ u(n) ≤ u(k) \\tag{5} \\]
Por tanto,
\\begin{align}
   u(k) - a &≤ |u(k) - a|    \\\\
            &< u(n) - a      &&\\text{[por (4)]} \\\\
            &≤ u(k) - a      &&\\text{[por (5)]}
\\end{align}
Luego,
\\[ u(k) - a < u(k) - a \\]
que es una contradicción.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {u : ℕ → ℝ}
variable (a : ℝ)

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def no_decreciente (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by
  intro n
  -- n : ℕ
  -- ⊢ u n ≤ a
  by_contra H
  -- H : ¬u n ≤ a
  -- ⊢ False
  push_neg at H
  -- H : a < u n
  replace H : u n - a > 0 := sub_pos.mpr H
  cases' h (u n - a) H with m hm
  -- m : ℕ
  -- hm : ∀ (n_1 : ℕ), n_1 ≥ m → |u n_1 - a| < u n - a
  let k := max n m
  have h1 : k ≥ n := le_max_left n m
  have h2 : k ≥ m := le_max_right n m
  have h3 : u k - a < u k - a := by
    calc u k  - a ≤ |u k - a| := by exact le_abs_self (u k - a)
                _ < u n - a   := hm k h2
                _ ≤ u k - a   := sub_le_sub_right (h' n k h1) a
  exact gt_irrefl (u k - a) h3

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by
  intro n
  -- n : ℕ
  -- ⊢ u n ≤ a
  by_contra H
  -- H : ¬u n ≤ a
  -- ⊢ False
  push_neg at H
  -- H : a < u n
  replace H : u n - a > 0 := sub_pos.mpr H
  cases' h (u n - a) H with m hm
  -- m : ℕ
  -- hm : ∀ (n_1 : ℕ), n_1 ≥ m → |u n_1 - a| < u n - a
  let k := max n m
  specialize hm k (le_max_right _ _)
  -- hm : |u k - a| < u n - a
  specialize h' n k (le_max_left _ _)
  -- h' : u n ≤ u k
  replace hm : |u k - a| < u k - a := by
    calc |u k - a| < u n - a := by exact hm
                 _ ≤ u k - a := sub_le_sub_right h' a
  rw [← not_le] at hm
  -- hm : ¬u k - a ≤ |u k - a|
  apply hm
  -- ⊢ u k - a ≤ |u k - a|
  exact le_abs_self (u k - a)

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
by
  intro n
  -- n : ℕ
  -- ⊢ u n ≤ a
  by_contra H
  -- H : ¬u n ≤ a
  -- ⊢ False
  push_neg at H
  -- H : a < u n
  cases' h (u n - a) (by linarith) with m hm
  -- m : ℕ
  -- hm : ∀ (n_1 : ℕ), n_1 ≥ m → |u n_1 - a| < u n - a
  specialize hm (max n m) (le_max_right _ _)
  -- hm : |u (max n m) - a| < u n - a
  specialize h' n (max n m) (le_max_left _ _)
  -- h' : u n ≤ u (max n m)
  rw [abs_lt] at hm
  -- hm : -(u n - a) < u (max n m) - a ∧ u (max n m) - a < u n - a
  linarith

-- Lemas usados
-- ============

-- variable (b : ℝ)
-- #check (abs_lt: |a| < b ↔ -b < a ∧ a < b)
-- #check (gt_irrefl a : ¬(a > a))
-- #check (le_abs_self a : a ≤ |a|)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (sub_le_sub_right : a ≤ b → ∀ (c : ℝ), a - c ≤ b - c)
-- #check (sub_pos : 0 < a - b ↔ b < a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limite_de_sucesiones_no_decrecientes.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Limite_de_sucesiones_no_decrecientes
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition no_decreciente :: "(nat ⇒ real) ⇒ bool"
  where "no_decreciente u ⟷ (∀ n m. n ≤ m ⟶ u n ≤ u m)"

(* 1ª demostración *)

lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "∀ n. u n ≤ a"
proof (rule allI)
  fix n
  show "u n ≤ a"
  proof (rule ccontr)
    assume "¬ u n ≤ a"
    then have "a < u n"
      by (rule not_le_imp_less)
    then have H : "u n - a > 0"
      by (simp only: diff_gt_0_iff_gt)
    then obtain m where hm : "∀p≥m. ¦u p - a¦ < u n - a"
      using assms(1) limite_def by blast
    let ?k = "max n m"
    have "n ≤ ?k"
      by (simp only: assms(2) no_decreciente_def)
    then have "u n ≤ u ?k"
      using assms(2) no_decreciente_def by blast
    have "¦u ?k - a¦ < u n - a"
      by (simp only: hm)
    also have "… ≤ u ?k - a"
      using ‹u n ≤ u ?k› by (rule diff_right_mono)
    finally have "¦u ?k - a¦ < u ?k - a"
      by this
    then have "¬ u ?k - a ≤ ¦u ?k - a¦"
      by (simp only: not_le_imp_less)
    moreover have "u ?k - a ≤ ¦u ?k - a¦"
      by (rule abs_ge_self)
    ultimately show False
      by (rule notE)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "∀ n. u n ≤ a"
proof (rule allI)
  fix n
  show "u n ≤ a"
  proof (rule ccontr)
    assume "¬ u n ≤ a"
    then have H : "u n - a > 0"
      by simp
    then obtain m where hm : "∀p≥m. ¦u p - a¦ < u n - a"
      using assms(1) limite_def by blast
    let ?k = "max n m"
    have "¦u ?k - a¦ < u n - a"
      using hm by simp
    moreover have "u n ≤ u ?k"
      using assms(2) no_decreciente_def by simp
    ultimately have "¦u ?k - a¦ < u ?k - a"
      by simp
    then show False
      by simp
  qed
qed

(* 3ª demostración *)

lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "∀ n. u n ≤ a"
proof
  fix n
  show "u n ≤ a"
  proof (rule ccontr)
    assume "¬ u n ≤ a"
    then obtain m where hm : "∀p≥m. ¦u p - a¦ < u n - a"
      using assms(1) limite_def by fastforce
    let ?k = "max n m"
    have "¦u ?k - a¦ < u n - a"
      using hm by simp
    moreover have "u n ≤ u ?k"
      using assms(2) no_decreciente_def by simp
    ultimately show False
      by simp
  qed
qed

end
</pre>
