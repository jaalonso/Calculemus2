---
title: Las sucesiones convergentes están acotadas
date: 2024-05-28 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(u_n\\) es una sucesión convergente, entonces está acotada; es decir,
\\[ (∃ k ∈ ℕ)(∃ b ∈ ℝ)(∀ n ∈ ℕ)[n ≥ k → |u_n| ≤ b] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| ≤ ε

-- (convergente u) expresa que u es convergente.
def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Puesto que la sucesión \\(u_n\\) es convergente, existe un \\(a ∈ ℝ\\) tal que
\\[ \\lim(u_n) = a \\]
Luego, existe un \\(k ∈ ℕ\\) tal que
\\[ (∀ n ∈ ℕ)[n ≥ k → |u_n - a | < 1] \\tag{1} \\]
Veamos que
\\[ (∀ n ∈ ℕ)[n ≥ k → |u_n| ≤ 1 + |a]] \\]
Para ello, sea \\(n ∈ ℕ\\) tal que
\\[ n ≥ k \\tag{2} \\]
Entonces,
\\begin{align}
   |u_n| &= |u_n - a + a|    \\\\
         &≤ |u_n - a| + |a|  \\\\
         &≤ 1 + |a|          &&\\text{[por (1) y (2)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {u : ℕ → ℝ}

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| ≤ ε

-- (convergente u) expresa que u es convergente.
def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

-- 1ª demostración
-- ===============

example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
by
  cases' h with a ua
  -- a : ℝ
  -- ua : limite u a
  cases' ua 1 zero_lt_one with k h
  -- k : ℕ
  -- h : ∀ (n : ℕ), n ≥ k → |u n - a| ≤ 1
  use k, 1 + |a|
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n| ≤ 1 + |a|
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n| ≤ 1 + |a|
  specialize h n hn
  -- ⊢ |u n| ≤ 1 + |a|
  calc |u n|
       = |u n - a + a|   := congr_arg abs (eq_add_of_sub_eq rfl)
     _ ≤ |u n - a| + |a| := abs_add (u n - a) a
     _ ≤ 1 + |a|         := add_le_add_right h |a|

-- 2ª demostración
-- ===============

example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
by
  cases' h with a ua
  -- a : ℝ
  -- ua : limite u a
  cases' ua 1 zero_lt_one with k h
  -- k : ℕ
  -- h : ∀ (n : ℕ), n ≥ k → |u n - a| ≤ 1
  use k, 1 + |a|
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n| ≤ 1 + |a|
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n| ≤ 1 + |a|
  specialize h n hn
  -- h : |u n - a| ≤ 1
  calc |u n|
       = |u n - a + a|   := by ring_nf
     _ ≤ |u n - a| + |a| := abs_add (u n - a) a
     _ ≤ 1 + |a|         := by linarith

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (add_le_add_right : b ≤ c → ∀ a,  b + a ≤ c + a)
-- #check (eq_add_of_sub_eq :  a - c = b → a = b + c)
-- #check (zero_lt_one : 0 < 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Acotacion_de_convergentes.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Acotacion_de_convergentes
imports Main HOL.Real
begin

(* (limite u c) expresa que el límite de u es c. *)
definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

(* (convergente u) expresa que u es convergente. *)
definition convergente :: "(nat ⇒ real) ⇒ bool" where
  "convergente u ⟷ (∃ a. limite u a)"

(* 1ª demostración *)

lemma
  assumes "convergente u"
  shows   "∃ k b. ∀n≥k. ¦u n¦ ≤ b"
proof -
  obtain a where "limite u a"
    using assms convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ 1"
    using limite_def zero_less_one by blast
  have "∀n≥k. ¦u n¦ ≤ 1 + ¦a¦"
  proof (intro allI impI)
    fix n
    assume hn : "n ≥ k"
    have "¦u n¦ = ¦u n - a + a¦"     by simp
    also have "… ≤ ¦u n - a¦ + ¦a¦" by simp
    also have "… ≤ 1 + ¦a¦"         by (simp add: hk hn)
    finally show "¦u n¦ ≤ 1 + ¦a¦"  .
  qed
  then show "∃ k b. ∀n≥k. ¦u n¦ ≤ b"
    by (intro exI)
qed

end
</pre>
