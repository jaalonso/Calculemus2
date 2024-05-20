---
title: Si una función es creciente e involutiva, entonces es la identidad
date: 2024-05-22 06:00:00 UTC+02:00
category: Funciones_reales
has_math: true
---

[mathjax]

Sea una función \\(f\\) de \\(ℝ\\) en \\(ℝ\\).

+ Se dice que \\(f\\) es creciente si para todo \\(x\\) e \\(y\\) tales que \\(x ≤ y\\) se tiene que \\(f(x) ≤ f(y)\\).
+ Se dice que \\(f\\) es involutiva si para todo \\(x\\) se tiene que \\(f(f(x)) = x\\).

En Lean4 que \\(f\\) sea creciente se representa por `Monotone f` y que sea involutiva por `Involutive f`

Demostrar con Lean4 que si \\(f\\) es creciente e involutiva, entonces \\(f\\) es la identidad.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

variable (f : ℝ → ℝ)

example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para todo \\(x ∈ ℝ\\), \\(f(x) = x\\). Sea \\(x ∈ ℝ\\). Entonces, por ser \\(f\\) involutiva, se tiene que
\\[ f(f(x)) = x \\tag{1} \\]
Además, por las propiedades del orden, se tiene que \\(f(x) ≤ x\\) ó \\(x ≤ f(x)\\). Demostraremos que \\(f(x) = x\\) en los dos casos.

Caso 1: Supongamos que
\\[ f(x) ≤ x \\tag{2} \\]
Entonces, por ser \\(f\\) creciente, se tiene que
\\[ f(f(x)) ≤ f(x) \\tag{3} \\]
Sustituyendo (1) en (3), se tiene
\\[ x ≤ f(x) \\]
que junto con (1) da
\\[ f(x) = x \\]

Caso 2: Supongamos que
\\[ x ≤ f(x) \\tag{4} \\]
Entonces, por ser \\(f\\) creciente, se tiene que
\\[ f(x) ≤ f(f(x)) \\tag{5} \\]
Sustituyendo (1) en (5), se tiene
\\[ f(x) ≤ x \\]
que junto con (4) da
\\[ f(x) = x \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  have h : f (f x) = x := hi x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    have h1a : f (f x) ≤ f x := hc h1
    have h1b : x ≤ f x := by rwa [h] at h1a
    show f x = x
    exact antisymm h1 h1b
  . -- h2 : x ≤ f x
    have h2a : f x ≤ f (f x) := hc h2
    have h2b : f x ≤ x := by rwa [h] at h2a
    show f x = x
    exact antisymm h2b h2

-- 2ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  unfold Monotone Involutive at *
  -- hc : ∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b
  -- hi : ∀ (x : ℝ), f (f x) = x
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  unfold id
  -- ⊢ f x = x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    apply antisymm h1
    -- ⊢ x ≤ f x
    have h3 : f (f x) ≤ f x := by
      apply hc
      -- ⊢ f x ≤ x
      exact h1
    rwa [hi] at h3
  . -- h2 : x ≤ f x
    apply antisymm _ h2
    -- ⊢ f x ≤ x
    have h4 : f x ≤ f (f x) := by
      apply hc
      -- ⊢ x ≤ f x
      exact h2
    rwa [hi] at h4

-- 3ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    apply antisymm h1
    -- ⊢ x ≤ f x
    have h3 : f (f x) ≤ f x := hc h1
    rwa [hi] at h3
  . -- h2 : x ≤ f x
    apply antisymm _ h2
    -- ⊢ f x ≤ x
    have h4 : f x ≤ f (f x) := hc h2
    rwa [hi] at h4

-- 4ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    apply antisymm h1
    -- ⊢ x ≤ f x
    calc x
         = f (f x) := (hi x).symm
       _ ≤ f x     := hc h1
  . -- h2 : x ≤ f x
    apply antisymm _ h2
    -- ⊢ f x ≤ x
    calc f x
         ≤ f (f x) := hc h2
       _ = x       := hi x

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (le_total a b : a ≤ b ∨ b ≤ a)
-- #check (antisymm : a ≤ b → b ≤ a → a = b)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Una_funcion_creciente_e_involutiva_es_la_identidad.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Una_funcion_creciente_e_involutiva_es_la_identidad
imports Main HOL.Real
begin

definition involutiva :: "(real ⇒ real) ⇒ bool"
  where "involutiva f ⟷ (∀x. f (f x) = x)"

(* 1ª demostración *)

lemma
  fixes f :: "real ⇒ real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof (unfold fun_eq_iff; intro allI)
  fix x
  have "x ≤ f x ∨ f x ≤ x"
    by (rule linear)
  then have "f x = x"
  proof (rule disjE)
    assume "x ≤ f x"
    then have "f x ≤ f (f x)"
      using assms(1) by (simp only: monoD)
    also have "… = x"
      using assms(2) by (simp only: involutiva_def)
    finally have "f x ≤ x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by (simp only: antisym)
  next
    assume "f x ≤ x"
    have "x = f (f x)"
      using assms(2) by (simp only: involutiva_def)
    also have "... ≤ f x"
      using ‹f x ≤ x› assms(1) by (simp only: monoD)
    finally have "x ≤ f x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by (simp only: monoD)
  qed
  then show "f x = id x"
    by (simp only: id_apply)
qed

(* 2ª demostración *)

lemma
  fixes f :: "real ⇒ real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof
  fix x
  have "x ≤ f x ∨ f x ≤ x"
    by (rule linear)
  then have "f x = x"
  proof
    assume "x ≤ f x"
    then have "f x ≤ f (f x)"
      using assms(1) by (simp only: monoD)
    also have "… = x"
      using assms(2) by (simp only: involutiva_def)
    finally have "f x ≤ x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by auto
  next
    assume "f x ≤ x"
    have "x = f (f x)"
      using assms(2) by (simp only: involutiva_def)
    also have "... ≤ f x"
      by (simp add: ‹f x ≤ x› assms(1) monoD)
    finally have "x ≤ f x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by auto
  qed
  then show "f x = id x"
    by simp
qed

(* 3ª demostración *)

lemma
  fixes f :: "real ⇒ real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof
  fix x
  have "x ≤ f x ∨ f x ≤ x"
    by (rule linear)
  then have "f x = x"
  proof
    assume "x ≤ f x"
    then have "f x ≤ x"
      by (metis assms involutiva_def mono_def)
    then show "f x = x"
      using ‹x ≤ f x› by auto
  next
    assume "f x ≤ x"
    then have "x ≤ f x"
      by (metis assms involutiva_def mono_def)
    then show "f x = x"
      using ‹f x ≤ x› by auto
  qed
  then show "f x = id x"
    by simp
qed

end
</pre>
