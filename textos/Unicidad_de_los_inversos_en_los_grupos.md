---
title: Si G es un grupo y a, b ∈ G tales que ab = 1 entonces a⁻¹ = b
date: 2024-05-13 06:00:00 UTC+02:00
category: Grupos
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(a\\) es un elemento de un grupo \\(G\\), entonces \\(a\\) tiene un único inverso; es decir, si \\(b\\) es un elemento de \\(G\\) tal que \\(a·b = 1\\), entonces \\(a⁻¹ = b\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a b : G}

example
  (h : a * b = 1)
  : a⁻¹ = b :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por la siguiente cadena de igualdades
\\begin{align}
   a⁻¹ &= a⁻¹·1        &&\\text{[porque 1 es neutro]} \\\\
       &= a⁻¹·(a·b)    &&\\text{[por hipótesis]} \\\\
       &= (a⁻¹·a)·b    &&\\text{[por la asociativa]} \\\\
       &= 1·b          &&\\text{[porque a⁻¹ es el inverso de a]} \\\\
       &= b            &&\\text{[porque 1 es neutro]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a b : G}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1  := (mul_one a⁻¹).symm
  _ = a⁻¹ * (a * b) := congrArg (a⁻¹ * .) h.symm
  _ = (a⁻¹ * a) * b := (mul_assoc a⁻¹ a b).symm
  _ = 1 * b         := congrArg (. * b) (inv_mul_self a)
  _ = b             := one_mul b

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       := by simp only [mul_one]
       _ = a⁻¹ * (a * b) := by simp only [h]
       _ = (a⁻¹ * a) * b := by simp only [mul_assoc]
       _ = 1 * b         := by simp only [inv_mul_self]
       _ = b             := by simp only [one_mul]

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       := by simp
       _ = a⁻¹ * (a * b) := by simp [h]
       _ = (a⁻¹ * a) * b := by simp
       _ = 1 * b         := by simp
       _ = b             := by simp

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * (a * b) := by simp [h]
       _ = b             := by simp

-- 5ª demostración
-- ===============

example
  (h : b * a = 1)
  : b = a⁻¹ :=
eq_inv_iff_mul_eq_one.mpr h

-- Lemas usados
-- ============

-- variable (c : G)
-- #check (eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1)
-- #check (inv_mul_self a : a⁻¹ * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Unicidad_de_los_inversos_en_los_grupos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Unicidad_de_los_inversos_en_los_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
proof -
  have "inverse a = inverse a * 1"    by (simp only: right_neutral)
  also have "… = inverse a * (a * b)" by (simp only: assms(1))
  also have "… = (inverse a * a) * b" by (simp only: assoc [symmetric])
  also have "… = 1 * b"               by (simp only: left_inverse)
  also have "… = b"                   by (simp only: left_neutral)
  finally show "inverse a = b"        by this
qed

(* 2ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
proof -
  have "inverse a = inverse a * 1"    by simp
  also have "… = inverse a * (a * b)" using assms by simp
  also have "… = (inverse a * a) * b" by (simp add: assoc [symmetric])
  also have "… = 1 * b"               by simp
  also have "… = b"                   by simp
  finally show "inverse a = b"        .
qed

(* 3ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
proof -
  from assms have "inverse a * (a * b) = inverse a"
    by simp
  then show "inverse a = b"
    by (simp add: assoc [symmetric])
qed

(* 4ª demostración *)

lemma
  assumes "a * b = 1"
  shows "inverse a = b"
  using assms
  by (simp only: inverse_unique)

end

end
</pre>
