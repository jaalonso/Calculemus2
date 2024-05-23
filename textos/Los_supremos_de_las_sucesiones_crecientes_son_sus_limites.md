---
title: Los supremos de las sucesiones crecientes son sus límites
date: 2024-05-24 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

Sea \\(u\\) una sucesión creciente. Demostrar con Lean4 que si \\(S\\) es un supremo de \\(u\\), entonces el límite de \\(u\\) es \\(S\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (u : ℕ → ℝ)
variable (S : ℝ)

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - c| ≤ ε

-- (supremo u S) expresa que el supremo de u es S.
def supremo (u : ℕ → ℝ) (S : ℝ) :=
  (∀ n, u n ≤ S) ∧ ∀ ε > 0, ∃ k, u k ≥ S - ε

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(ε ∈ ℝ\\) tal que \\(ε > 0\\). Tenemos que demostrar que
\\[ (∃ m ∈ ℕ)(∀ n ∈ ℕ)[n ≥ m → |u_n - S| ≤ ε] \\tag{1} \\]

Por ser \\(S\\) un supremo de u, existe un k ∈ ℕ tal que
\\[ u_k ≥ S - ε \\tag{2} \\]
Vamos a demostrar que \\(k\\) verifica la condición de (1); es decir, que si \\(n ∈ ℕ\\) tal que \\(n ≥ k\\), entonces
\\[ |u_n - S| ≤ ε \\]
o, equivalentemente,
\\[ -ε ≤ u_n - S ≤ ε \\]

La primera desigualdad se tiene por la siguente cadena:
\\begin{align}
   -ε &= (S - ε) - S    \\\\
      &≤ u_k - S         &&\\text{[por (2)]} \\\\
      &≤ u_n - S         &&\\text{[porque \\(u\\) es creciente y \\(n ≥ k\\)]}
\\end{align}

La segunda desigualdad se tiene por la siguente cadena:
\\begin{align}
   u_n - S &≤ S - S      &&\\text{[porque \\(S\\) es un supremo de \\(u\\)]} \\\\
          &= 0          \\\\
          &≤ ε
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (u : ℕ → ℝ)
variable (S : ℝ)

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - c| ≤ ε

-- (supremo u S) expresa que el supremo de u es S.
def supremo (u : ℕ → ℝ) (S : ℝ) :=
  (∀ n, u n ≤ S) ∧ ∀ ε > 0, ∃ k, u k ≥ S - ε

-- 1ª demostración
-- ===============

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by
  unfold limite
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  unfold supremo at hS
  -- hS : (∀ (n : ℕ), u n ≤ S) ∧ ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS with hS₁ hS₂
  -- hS₁ : ∀ (n : ℕ), u n ≤ S
  -- hS₂ : ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS₂ ε hε with k hk
  -- k : ℕ
  -- hk : u k ≥ S - ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n - S| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n - S| ≤ ε
  rw [abs_le]
  -- ⊢ -ε ≤ u n - S ∧ u n - S ≤ ε
  constructor
  . -- ⊢ -ε ≤ u n - S
    unfold Monotone at hu
    -- hu : ∀ ⦃a b : ℕ⦄, a ≤ b → u a ≤ u b
    specialize hu hn
    -- hu : u k ≤ u n
    calc -ε
         = (S - ε) - S := by ring
       _ ≤ u k - S     := sub_le_sub_right hk S
       _ ≤ u n - S     := sub_le_sub_right hu S
  . calc u n - S
         ≤ S - S       := sub_le_sub_right (hS₁ n) S
       _ = 0           := sub_self S
       _ ≤ ε           := le_of_lt hε

-- 2ª demostración
-- ===============

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  cases' hS with hS₁ hS₂
  -- hS₁ : ∀ (n : ℕ), u n ≤ S
  -- hS₂ : ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS₂ ε hε with k hk
  -- k : ℕ
  -- hk : u k ≥ S - ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n - S| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n - S| ≤ ε
  rw [abs_le]
  -- ⊢ -ε ≤ u n - S ∧ u n - S ≤ ε
  constructor
  . -- ⊢ -ε ≤ u n - S
    linarith [hu hn]
  . -- ⊢ u n - S ≤ ε
    linarith [hS₁ n]

-- 3ª demostración
-- ===============

example
  (hu : Monotone u)
  (hS : supremo u S)
  : limite u S :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ m, ∀ (n : ℕ), n ≥ m → |u n - S| ≤ ε
  cases' hS with hS₁ hS₂
  -- hS₁ : ∀ (n : ℕ), u n ≤ S
  -- hS₂ : ∀ (ε : ℝ), ε > 0 → ∃ k, u k ≥ S - ε
  cases' hS₂ ε hε with k hk
  -- k : ℕ
  -- hk : u k ≥ S - ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n - S| ≤ ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n - S| ≤ ε
  rw [abs_le]
  -- ⊢ -ε ≤ u n - S ∧ u n - S ≤ ε
  constructor <;> linarith [hu hn, hS₁ n]

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b)
-- #check (le_of_lt : a < b → a ≤ b)
-- #check (sub_le_sub_right : a ≤ b → ∀ (c : ℝ), a - c ≤ b - c)
-- #check (sub_self a : a - a = 0)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Los_supremos_de_las_sucesiones_crecientes_son_sus_limites
imports Main HOL.Real
begin

(* (limite u c) expresa que el límite de u es c. *)
definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

(* (supremo u M) expresa que el supremo de u es M. *)
definition supremo :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "supremo u M ⟷ ((∀n. u n ≤ M) ∧ (∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε))"

(* 1ª demostración *)

lemma
  assumes "mono u"
          "supremo u M"
  shows   "limite u M"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  have hM : "((∀n. u n ≤ M) ∧ (∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε))"
    using assms(2)
    by (simp add: supremo_def)
  then have "∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε"
    by (rule conjunct2)
  then have "∃k. ∀n≥k. u n ≥ M - ε"
    by (simp only: ‹0 < ε›)
  then obtain n0 where "∀n≥n0. u n ≥ M - ε"
    by (rule exE)
  have "∀n≥n0. ¦u n - M¦ ≤ ε"
  proof (intro allI impI)
    fix n
    assume "n ≥ n0"
    show "¦u n - M¦ ≤ ε"
    proof (rule abs_leI)
      have "∀n. u n ≤ M"
        using hM by (rule conjunct1)
      then have "u n - M ≤ M - M"
        by simp
      also have "… = 0"
        by (simp only: diff_self)
      also have "… ≤ ε"
        using ‹0 < ε› by (simp only: less_imp_le)
      finally show "u n - M ≤ ε"
        by this
    next
      have "-ε = (M - ε) - M"
        by simp
      also have "… ≤ u n - M"
        using ‹∀n≥n0. M - ε ≤ u n› ‹n0 ≤ n› by auto
      finally have "-ε ≤ u n - M"
        by this
      then show "- (u n - M) ≤ ε"
        by simp
    qed
  qed
  then show "∃k. ∀n≥k. ¦u n - M¦ ≤ ε"
    by (rule exI)
qed

(* 2ª demostración *)

lemma
  assumes "mono u"
          "supremo u M"
  shows   "limite u M"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  have hM : "((∀n. u n ≤ M) ∧ (∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε))"
    using assms(2)
    by (simp add: supremo_def)
  then have "∃k. ∀n≥k. u n ≥ M - ε"
    using ‹0 < ε› by presburger
  then obtain n0 where "∀n≥n0. u n ≥ M - ε"
    by (rule exE)
  then have "∀n≥n0. ¦u n - M¦ ≤ ε"
    using hM by auto
  then show "∃k. ∀n≥k. ¦u n - M¦ ≤ ε"
    by (rule exI)
qed

end
</pre>
