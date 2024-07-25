---
title: Las sucesiones divergentes positivas no_tienen límites finitos
date: 2024-07-26 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, una sucesión \\(u_0, u_1, u_2, ...\\) se puede representar mediante una función \\(u : ℕ → ℝ\\) de forma que \\(u(n)\\) es \\(uₙ\\).

Se define que \\(a\\) es el límite de la sucesión \\(u\\), por
<pre lang="haskell">
   def limite (u: ℕ → ℝ) (a: ℝ) :=
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>

La sucesión \\(u\\) diverge positivamente cuando, para cada número real \\(A\\), se puede encontrar un número natural \\(m\\) tal que si \\(n ≥ m\\), entonces \\(uₙ > A\\). En Lean se puede definir por
<pre lang="haskell">
   def diverge_positivamente (u : ℕ → ℝ) :=
     ∀ A, ∃ m, ∀ n ≥ m, u n > A
</pre>

Demostrar que si \\(u\\) diverge positivamente, entonces ningún número real es límite de \\(u\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {u : ℕ → ℝ}

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def diverge_positivamente (u : ℕ → ℝ) :=
  ∀ A, ∃ m, ∀ n ≥ m, u n > A

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Supongamos que existe un \\(a ∈ ℝ\\) tal que \\(a\\) es límite de \\(u\\). Entonces, existe un \\(m_1 ∈ ℕ\\) tal que
\\[ (∀ n ≥ m_1) |u_n - a| < 1 \\tag{1} \\]
Puesto que \\(u\\) diverge positivamente, existe un \\(m_2 ∈ ℕ\\) tal que
\\[ (∀ n ≥ m_2) u_n > a + 1 \\tag{2} \\]
Sea \\(m\\) el máximo de \\(m_1\\) y \\(m_2\\). Entonces,
\\begin{align}
   m &≥ m_1 \\tag{3} \\\\
   m &≥ m_2 \\tag{4}
\\end{align}
Por (1) y (3), se tiene que
\\[ |u_m - a| < 1 \\]
Luego,
\\[ u_m - a < 1 \\tag{5} \\]
Por (2) y (4), se tiene que
\\[ u_m > a + 1 \\tag{6} \\]
Por tanto,
\\begin{align}
   u_m &< a + 1       &&\\text{[por (5)]} \\\\
      &< u_m          &&\\text{[por (6)]}
\\end{align}
De donde se tiene que
\\[ u_m < u_m \\]
que es una contradicción.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {u : ℕ → ℝ}

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def diverge_positivamente (u : ℕ → ℝ) :=
  ∀ A, ∃ m, ∀ n ≥ m, u n > A

-- 1ª demostración
-- ===============

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by
  push_neg
  -- ⊢ ∀ (a : ℝ), ¬limite u a
  intros a ha
  -- a : ℝ
  -- ha : limite u a
  -- ⊢ False
  cases' ha 1 zero_lt_one with m1 hm1
  -- m1 : ℕ
  -- hm1 : ∀ (n : ℕ), n ≥ m1 → |u n - a| < 1
  cases' h (a+1) with m2 hm2
  -- m2 : ℕ
  -- hm2 : ∀ (n : ℕ), n ≥ m2 → u n > a + 1
  let m := max m1 m2
  specialize hm1 m (le_max_left _ _)
  -- hm1 : |u m - a| < 1
  specialize hm2 m (le_max_right _ _)
  -- hm2 : u m > a + 1
  replace hm1 : u m - a < 1 := lt_of_abs_lt hm1
  replace hm2 : 1 < u m - a := lt_sub_iff_add_lt'.mpr hm2
  apply lt_irrefl (u m)
  -- ⊢ u m < u m
  calc u m < a + 1 := by exact sub_lt_iff_lt_add'.mp hm1
         _ < u m   := lt_sub_iff_add_lt'.mp hm2

-- 2ª demostración
-- ===============

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by
  push_neg
  -- ⊢ ∀ (a : ℝ), ¬limite u a
  intros a ha
  -- a : ℝ
  -- ha : limite u a
  -- ⊢ False
  cases' ha 1 (by linarith) with m1 hm1
  -- m1 : ℕ
  -- hm1 : ∀ (n : ℕ), n ≥ m1 → |u n - a| < 1
  cases' h (a+1) with m2 hm2
  -- m2 : ℕ
  -- hm2 : ∀ (n : ℕ), n ≥ m2 → u n > a + 1
  let m := max m1 m2
  replace hm1 : |u m - a| < 1 := by aesop
  replace hm1 : u m - a < 1   := lt_of_abs_lt hm1
  replace hm2 : a + 1 < u m   := by aesop
  replace hm2 : 1 < u m - a   := lt_sub_iff_add_lt'.mpr hm2
  apply lt_irrefl (u m)
  -- ⊢ u m < u m
  calc u m < a + 1 := by linarith
         _ < u m   := by linarith

-- 3ª demostración
-- ===============

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
by
  push_neg
  -- ⊢ ∀ (a : ℝ), ¬limite u a
  intros a ha
  -- a : ℝ
  -- ha : limite u a
  -- ⊢ False
  cases' ha 1 (by linarith) with m1 hm1
  -- m1 : ℕ
  -- hm1 : ∀ (n : ℕ), n ≥ m1 → |u n - a| < 1
  cases' h (a+1) with m2 hm2
  -- m2 : ℕ
  -- hm2 : ∀ (n : ℕ), n ≥ m2 → u n > a + 1
  let m := max m1 m2
  specialize hm1 m (le_max_left _ _)
  -- hm1 : |u m - a| < 1
  rw [abs_lt] at hm1
  -- hm1 : -1 < u m - a ∧ u m - a < 1
  specialize hm2 m (le_max_right _ _)
  -- hm2 : u m > a + 1
  linarith

-- Lemas usados
-- ============

-- variable (m n : ℕ)
-- variable (a b c : ℝ)
-- #check (abs_lt: |a| < b ↔ -b < a ∧ a < b)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (lt_irrefl a : ¬a < a)
-- #check (lt_of_abs_lt : |a| < b → a < b)
-- #check (lt_sub_iff_add_lt' : b < c - a ↔ a + b < c)
-- #check (sub_lt_iff_lt_add' : a - b < c ↔ a < b + c)
-- #check (zero_lt_one : 0 < 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition diverge_positivamente :: "(nat ⇒ real) ⇒ bool"
  where "diverge_positivamente u ⟷ (∀A. ∃m. ∀n≥m. u n > A)"

(* 1ª demostración *)

lemma
  assumes "diverge_positivamente u"
  shows   "∄a. limite u a"
proof (rule notI)
  assume "∃a. limite u a"
  then obtain a where "limite u a" try
    by auto
  then obtain m1 where hm1 : "∀n≥m1. ¦u n - a¦ < 1"
    using limite_def by fastforce
  obtain m2 where hm2 : "∀n≥m2. u n > a + 1"
    using assms diverge_positivamente_def by blast
  let ?m = "max m1 m2"
  have "u ?m < u ?m" using hm1 hm2
  proof -
    have "?m ≥ m1"
      by (rule max.cobounded1)
    have "?m ≥ m2"
      by (rule max.cobounded2)
    have "u ?m - a < 1"
      using hm1 ‹?m ≥ m1› by fastforce
    moreover have "u ?m > a + 1"
      using hm2 ‹?m ≥ m2› by simp
    ultimately show "u ?m < u ?m"
      by simp
  qed
  then show False
    by auto
qed

(* 2ª demostración *)

lemma
  assumes "diverge_positivamente u"
  shows   "∄a. limite u a"
proof (rule notI)
  assume "∃a. limite u a"
  then obtain a where "limite u a" try
    by auto
  then obtain m1 where hm1 : "∀n≥m1. ¦u n - a¦ < 1"
    using limite_def by fastforce
  obtain m2 where hm2 : "∀n≥m2. u n > a + 1"
    using assms diverge_positivamente_def by blast
  let ?m = "max m1 m2"
  have "1 < 1"
  proof -
    have "1 < u ?m - a"
      using hm2
      by (metis add.commute less_diff_eq max.cobounded2)
    also have "… < 1"
      using hm1
      by (metis abs_less_iff max_def order_refl)
    finally show "1 < 1" .
  qed
  then show False
    by auto
qed

end
</pre>
