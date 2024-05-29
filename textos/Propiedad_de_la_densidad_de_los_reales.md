---
title: Si x, y ∈ ℝ tales que (∀ z)[y < z → x ≤ z], entonces x ≤ y
date: 2024-05-30 06:00:00 UTC+02:00
category: Números reales
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(x, y ∈ ℝ\\) tales que \\((∀ z)[y < z → x ≤ z]\\), entonces \\(x ≤ y\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {x y : ℝ}

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Lo demostraremos por reducción al absurdo. Para ello, supongamos que
\\[ x ≰ y \\]
Entonces
\\[ y < x \\]
y, por la densidad de \\(ℝ\\), existe un \\(a\\) tal que
\\[ y < a < x \\]
Puesto que \\(y < a\\), por la hipótesis, se tiene que
\\[ x ≤ a \\]
en contradicción con
\\[ a < x \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable {x y : ℝ}

-- 1ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  by_contra h1
  -- h1 : ¬x ≤ y
  -- ⊢ False
  have hxy : x > y := not_le.mp h1
  -- ⊢ ¬x > y
  cases' (exists_between hxy) with a ha
  -- a : ℝ
  -- ha : y < a ∧ a < x
  apply (lt_irrefl a)
  -- ⊢ a < a
  calc a
       < x := ha.2
     _ ≤ a := h a ha.1

-- 2ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  cases' (exists_between hxy) with a ha
  -- a : ℝ
  -- ha : y < a ∧ a < x
  apply (lt_irrefl a)
  -- ⊢ a < a
  calc a
       < x := ha.2
     _ ≤ a := h a ha.1

-- 3ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  cases' (exists_between hxy) with a ha
  -- ha : y < a ∧ a < x
  apply (lt_irrefl a)
  -- ⊢ a < a
  exact lt_of_lt_of_le ha.2 (h a ha.1)

-- 4ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  cases' (exists_between hxy) with a ha
  -- a : ℝ
  -- ha : y < a ∧ a < x
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1))

-- 5ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
by
  apply le_of_not_gt
  -- ⊢ ¬x > y
  intro hxy
  -- hxy : x > y
  -- ⊢ False
  rcases (exists_between hxy) with ⟨a, hya, hax⟩
  -- a : ℝ
  -- hya : y < a
  -- hax : a < x
  exact (lt_irrefl a) (lt_of_lt_of_le hax (h a hya))

-- 6ª demostración
-- ===============

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_forall_le_of_dense h

-- Lemas usados
-- ============

-- variable (z : ℝ)
-- #check (exists_between : x < y → ∃ z, x < z ∧ z < y)
-- #check (le_of_forall_le_of_dense : (∀ z, y < z → x ≤ z) → x ≤ y)
-- #check (le_of_not_gt : ¬x > y → x ≤ y)
-- #check (lt_irrefl x : ¬x < x)
-- #check (lt_of_lt_of_le : x < y → y ≤ z → x < z)
-- #check (not_le : ¬x ≤ y ↔ y < x)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_de_la_densidad_de_los_reales.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Propiedad_de_la_densidad_de_los_reales
imports Main HOL.Real
begin

(* 1ª demostración *)

lemma
  fixes x y :: real
  assumes "∀ z. y < z ⟶ x ≤ z"
  shows "x ≤ y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "∃z. y < z ∧ z < x"
    by (rule dense)
  then obtain a where ha : "y < a ∧ a < x"
    by (rule exE)
  have "¬ a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
  proof -
    have "y < a ⟶ x ≤ a"
      using assms by (rule allE)
    moreover
    have "y < a"
      using ha by (rule conjunct1)
    ultimately have "x ≤ a"
      by (rule mp)
    moreover
    have "a < x"
      using ha by (rule conjunct2)
    ultimately show "a < a"
      by (simp only: less_le_trans)
  qed
  ultimately show False
    by (rule notE)
qed

(* 2ª demostración *)

lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "∃z. y < z ∧ z < x"
    by (rule dense)
  then obtain a where hya : "y < a" and hax : "a < x"
    by auto
  have "¬ a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
  proof -
    have "a < x"
      using hax .
    also have "… ≤ a"
      using assms[OF hya] .
    finally show "a < a" .
  qed
  ultimately show False
    by (rule notE)
qed

(* 3ª demostración *)

lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "∃z. y < z ∧ z < x"
    by (rule dense)
  then obtain a where hya : "y < a" and hax : "a < x"
    by auto
  have "¬ a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
    using hax assms[OF hya] by (rule less_le_trans)
  ultimately show False
    by (rule notE)
qed

(* 4ª demostración *)

lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
by (meson assms dense not_less)

(* 5ª demostración *)

lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
using assms by (rule dense_ge)

(* 6ª demostración *)

lemma
  fixes x y :: real
  assumes "∀ z. y < z ⟶ x ≤ z"
  shows "x ≤ y"
using assms by (simp only: dense_ge)

end
</pre>
