---
title: Las sucesiones convergentes son sucesiones de Cauchy
date: 2024-06-28 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, una sucesión (u_0, u_1, u_2, ...\) se puede representar mediante
una función \(u : ℕ → ℝ\) de forma que \(u(n)\) es \(uₙ\).

Se define

+ \(a\) es un límite de la sucesión \(u\) , por
<pre lang="lean">
     def limite (u : ℕ → ℝ) (a : ℝ) :=
       ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| ≤ ε
</pre>
+ la sucesión \(u\) es convergente por
<pre lang="lean">
     def suc_convergente (u : ℕ → ℝ) :=
       ∃ a, limite u a
</pre>
+ la sucesión \(u\) es de Cauchy por
<pre lang="lean">
     def suc_Cauchy (u : ℕ → ℝ) :=
       ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε
</pre>

Demostrar con Lean4 que las sucesiones convergentes son de Cauchy.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {u : ℕ → ℝ }

def limite (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def suc_Cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(ε ∈ ℝ\) tal que \(ε > 0\). Tenemos que demostrar que existe un \(N ∈ ℕ\) tal que
\[ (∀ p ≥ N)(∀ q ≥ N)[|u(p) - u(q)| < ε] \tag{1} \]

Puesto que \(u\) es convergente, existe un \(a ∈ ℝ\) tal que el límite de \(u\) es \(a\). Por tanto, existe un \(N ∈ ℕ\) tal que
\[ (∀ n ≥ N)[|u(n) - a| < ε/2] tag{2} \]

Para demostrar que con dicho \(N\) se cumple (1), sean \(p, q ∈ ℕ\) tales que \(p ≥ N\) y \(q ≥ N\). Entonces, por (2), se tiene que
\begin{align}
   &|u(p) - a| < ε/2 \tag{3} \\
   &|u(q) - a| < ε/2 \tag{4}
\end{align}

Por tanto,
\begin{align}
   |u(p) - u(q)| &= |(u(p) - a) + (a - u(q))|    \\
                 &≤ |u(p) - a|  + |a - u(q)|     \\
                 &= |u(p) - a|  + |u(q) - a|     \\
                 &< ε/2 + ε/2                    &&\text{[por (3) y (4)} \\
                 &= ε
\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {u : ℕ → ℝ }

def limite (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def suc_Cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

-- 1ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  unfold suc_Cauchy
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  have hε2 : 0 < ε/2 := half_pos hε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) hε2 with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha hε2
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := congrArg (|u p - a| + .) (abs_sub_comm a (u q))
     _ < ε/2 + ε/2               := add_lt_add (hN p hp) (hN q hq)
     _ = ε                       := add_halves ε

-- 2ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := congrArg (|u p - a| + .) (abs_sub_comm a (u q))
     _ < ε/2 + ε/2               := add_lt_add (hN p hp) (hN q hq)
     _ = ε                       := add_halves ε

-- 3ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  have cota1 : |u p - a| < ε / 2 := hN p hp
  have cota2 : |u q - a| < ε / 2 := hN q hq
  clear hN hp hq
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := by rw [abs_sub_comm a (u q)]
     _ < ε                       := by linarith

-- 4ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  clear hε ha
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := by rw [abs_sub_comm a (u q)]
     _ < ε                       := by linarith [hN p hp, hN q hq]

-- 5ª demostración
-- ===============

example
  (h : suc_convergente u)
  : suc_Cauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' h with a ha
  -- a : ℝ
  -- ha : limite u a
  cases' ha (ε/2) (by linarith) with N hN
  -- N : ℕ
  -- hN : ∀ (n : ℕ), n ≥ N → |u n - a| < ε / 2
  use N
  -- ⊢ ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  intros p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |u p - u q| < ε
  calc |u p - u q|
       = |(u p - a) + (a - u q)| := by ring_nf
     _ ≤ |u p - a|  + |a - u q|  := abs_add (u p - a) (a - u q)
     _ = |u p - a|  + |u q - a|  := by simp [abs_sub_comm]
     _ < ε                       := by linarith [hN p hp, hN q hq]

-- Lemas usados
-- ============

-- variable (a b c d x y : ℝ)
-- variable (f : ℝ → ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_sub_comm a b : |a - b| = |b - a|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (add_lt_add : a < b → c < d → a + c < b + d)
-- #check (congrArg f : x = y → f x = f y)
-- #check (half_pos : 0 < a → 0 < a / 2)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_sucesiones_convergentes_son_sucesiones_de_Cauchy
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

definition suc_convergente :: "(nat ⇒ real) ⇒ bool"
  where "suc_convergente u ⟷ (∃ l. limite u l)"

definition suc_cauchy :: "(nat ⇒ real) ⇒ bool"
  where "suc_cauchy u ⟷ (∀ε>0. ∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε)"

(* 1ª demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  have "∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
  proof (intro allI impI)
    fix p q
    assume hp : "p ≥ k" and hq : "q ≥ k"
    then have hp' : "¦u p - a¦ < ε/2"
      using hk by blast
    have hq' : "¦u q - a¦ < ε/2"
      using hk hq by blast
    have "¦u p - u q¦ = ¦(u p - a) + (a - u q)¦"
      by simp
    also have "… ≤ ¦u p - a¦  + ¦a - u q¦"
      by simp
    also have "… = ¦u p - a¦  + ¦u q - a¦"
      by simp
    also have "… < ε/2 + ε/2"
      using hp' hq' by simp
    also have "… = ε"
      by simp
    finally show "¦u p - u q¦ < ε"
      by this
  qed
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (rule exI)
qed

(* 2ª demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  have "∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
  proof (intro allI impI)
    fix p q
    assume hp : "p ≥ k" and hq : "q ≥ k"
    then have hp' : "¦u p - a¦ < ε/2"
      using hk by blast
    have hq' : "¦u q - a¦ < ε/2"
      using hk hq by blast
    show "¦u p - u q¦ < ε"
      using hp' hq' by argo
  qed
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (rule exI)
qed

(* 3ª demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  have "∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    using hk by (smt (z3) field_sum_of_halves)
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (rule exI)
qed

(* 4ª demostración *)

lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (smt (z3) field_sum_of_halves)
qed

end
</pre>
