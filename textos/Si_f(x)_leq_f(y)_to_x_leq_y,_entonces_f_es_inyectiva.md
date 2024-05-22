---
title: Si `f(x) ≤ f(y) → x ≤ y`, entonces f es inyectiva
date: 2024-05-23 06:00:00 UTC+02:00
category: Funciones_reales
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) una función de \\(ℝ\\) en \\(ℝ\\) tal que
\\[ (∀ x, y)[f(x) ≤ f(y) → x ≤ y] \\]
entonces \\(f\\) es inyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

variable (f : ℝ → ℝ)

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(x, y ∈ ℝ\\) tales que
\\[ f(x) = f(y) \\tag{1} \\]
Tenemos que demostrar que \\(x = y\\).

De (1), tenemos que
\\[ f(x) ≤ f(y) \\]
y, por la hipótesis,
\\[ x ≤ y \\tag{2} \\]

También de (1), tenemos que
\\[ f(y) ≤ f(x) \\]
y, por la hipótesis,
\\[ y ≤ x \\tag{3} \\]

De (2) y (3), tenemos que
\\[ x = y \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Function

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  have h1 : f x ≤ f y := le_of_eq hxy
  have h2 : x ≤ y     := h h1
  have h3 : f y ≤ f x := ge_of_eq hxy
  have h4 : y ≤ x     := h h3
  show x = y
  exact le_antisymm h2 h4

-- 2ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  have h1 : x ≤ y     := h (le_of_eq hxy)
  have h2 : y ≤ x     := h (ge_of_eq hxy)
  show x = y
  exact le_antisymm h1 h2

-- 3ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  show x = y
  exact le_antisymm (h (le_of_eq hxy)) (h (ge_of_eq hxy))

-- 3ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
fun _ _ hxy ↦ le_antisymm (h hxy.le) (h hxy.ge)

-- 4ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  apply le_antisymm
  . -- ⊢ x ≤ y
    apply h
    -- ⊢ f x ≤ f y
    exact le_of_eq hxy
  . -- ⊢ y ≤ x
    apply h
    -- ⊢ f y ≤ f x
    exact ge_of_eq hxy

-- 5ª demostración
-- ===============

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : Injective f :=
by
  intros x y hxy
  -- x y : ℝ
  -- hxy : f x = f y
  -- ⊢ x = y
  apply le_antisymm
  . -- ⊢ x ≤ y
    exact h (le_of_eq hxy)
  . -- ⊢ y ≤ x
    exact h (ge_of_eq hxy)

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (ge_of_eq : a = b → a ≥ b)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_of_eq : a = b → a ≤ b)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva"
imports Main HOL.Real
begin

(* 1ª demostración *)

lemma
  fixes f :: "real ⇒ real"
  assumes "∀ x y. f x ≤ f y ⟶ x ≤ y"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  show "x = y"
  proof (rule antisym)
    show "x ≤ y"
      by (simp only: assms ‹f x = f y›)
  next
    show "y ≤ x"
      by (simp only: assms ‹f x = f y›)
  qed
qed

(* 2ª demostración *)

lemma
  fixes f :: "real ⇒ real"
  assumes "∀ x y. f x ≤ f y ⟶ x ≤ y"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  then show "x = y"
    using assms
    by (simp add: eq_iff)
qed

(* 3ª demostración *)

lemma
  fixes f :: "real ⇒ real"
  assumes "∀ x y. f x ≤ f y ⟶ x ≤ y"
  shows   "inj f"
  by (simp add: assms injI eq_iff)
end
</pre>
