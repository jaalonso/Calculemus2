---
title: Unicidad del elemento neutro en los grupos
date: 2024-05-10 06:00:00 UTC+02:00
category: Grupos
has_math: true
---

[mathjax]

Demostrar con Lean4 que un grupo sólo posee un elemento neutro.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(e ∈ G\\) tal que
\\[ (∀ x)[x·e = x] \\tag{1} \\]
Entonces,
\\begin{align}
   e &= 1.e    &&\\text{[porque 1 es neutro]} \\\\
     &= 1      &&\\text{[por (1)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]

-- 1ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
calc e = 1 * e := (one_mul e).symm
     _ = 1     := h 1

-- 2ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
by
  have h1 : e = e * e := (h e).symm
  exact self_eq_mul_left.mp h1

-- 3ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
self_eq_mul_left.mp (h e).symm

-- 4ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
by aesop

-- Lemas usados
-- ============

-- variable (a b : G)
-- #check (one_mul a : 1 * a = a)
-- #check (self_eq_mul_left : b = a * b ↔ a = 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Unicidad_del_elemento_neutro_en_los_grupos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Unicidad_del_elemento_neutro_en_los_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma
  assumes "∀ x. x * e = x"
  shows   "e = 1"
proof -
  have "e = 1 * e"     by (simp only: left_neutral)
  also have "… = 1"    using assms by (rule allE)
  finally show "e = 1" by this
qed

(* 2ª demostración *)

lemma
  assumes "∀ x. x * e = x"
  shows   "e = 1"
proof -
  have "e = 1 * e"     by simp
  also have "… = 1"    using assms by simp
  finally show "e = 1" .
qed

(* 3ª demostración *)

lemma
  assumes "∀ x. x * e = x"
  shows   "e = 1"
  using assms
  by (metis left_neutral)

end

end
</pre>
