---
title: Si el límite de la sucesión uₙ es a, entonces el límite de -uₙ es -a
date: 2024-06-06 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, una sucesión \(u₀, u₁, u₂, ...\) se puede representar mediante una función \(u : ℕ → ℝ\) de forma que \(u(n)\) es \(uₙ\).

Se define que \(c\) es el límite de la sucesión \(u\), por
<pre lang="lean">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
</pre>

Demostrar con Lean4 que que si el límite de \(uₙ\) es \(a\), entonces el de \(-uₙ\) es \(-a\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (fun n ↦ -u n) (-a) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(ε ∈ ℝ\) tal que \(ε > 0\). Tenemos que demostrar que
\[ (∃ N ∈ ℕ)(∀ n ≥ N)[|-uₙ - -a| < ε] \tag{1} \]
Puesto que el límite de \(uₙ\) es \(a\), existe un \(k ∈ ℕ\) tal que
\[ (∀ n ≥ k)[|uₙ - a| < ε/|c| \tag{2} \]
Veamos que con \(k\) se cumple (1). En efecto, sea \(n ≥ k\). Entonces,
\begin{align}
   |-uₙ - -a| &= |-(uₙ - a)| \\
              &= |uₙ - a|    \\
              &< ε           &&\text{[por (2)]}
\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (fun n ↦ -u n) (-a) :=
by
  unfold limite at *
  -- h : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => -u n) n - -a| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun n => -u n) n - -a| < ε
  specialize h ε hε
  -- h : ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  cases' h with k hk
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |(fun n => -u n) n - -a| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(fun n => -u n) n - -a| < ε
  calc |(fun n => -u n) n - -a|
       = |(-u n - -a)|          := rfl
     _ = |(-(u n - a))|         := by congr ; ring
     _ = |(u n - a)|            := abs_neg (u n - a)
     _ < ε                      := hk n hn

-- Lemas usados
-- ============

-- #check (abs_neg a : |(-a)| = |a|)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limite_de_la_opuesta.lean).
