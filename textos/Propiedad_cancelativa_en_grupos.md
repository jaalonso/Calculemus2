---
title: Si G es un grupo y a, b, c ∈ G tales que a·b = a·c, entonces b = c
date: 2024-05-16 06:00:00 UTC+02:00
category: Grupos
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(G\\) es un grupo y \\(a, b, c ∈ G\\) tales que \\(a·b = a·c\\), entonces \\(b = c\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a b c : G}

example
  (h: a * b = a  * c)
  : b = c :=
sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por la siguiente cadena de igualdades
\\begin{align}
   b &= 1·b          &&\\text{[porque \\(1\\) es neutro]} \\\\
     &= (a⁻¹·a)·b    &&\\text{[porque \\(a⁻¹\\) es el inverso de \\(a\\)]} \\\\
     &= a⁻¹·(a·b)    &&\\text{[por la asociativa]} \\\\
     &= a⁻¹·(a·c)    &&\\text{[por la hipótesis]} \\\\
     &= (a⁻¹·a)·c    &&\\text{[por la asociativa]} \\\\
     &= 1·c          &&\\text{[porque \\(a⁻¹\\) es el inverso de \\(a\\)]} \\\\
     &= c            &&\\text{[porque 1 es neutro]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a b c : G}

-- 1ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         := (one_mul b).symm
     _ = (a⁻¹ * a) * b := congrArg (. * b) (inv_mul_self a).symm
     _ = a⁻¹ * (a * b) := mul_assoc a⁻¹ a b
     _ = a⁻¹ * (a * c) := congrArg (a⁻¹ * .) h
     _ = (a⁻¹ * a) * c := (mul_assoc a⁻¹ a c).symm
     _ = 1 * c         := congrArg (. * c) (inv_mul_self a)
     _ = c             := one_mul c

-- 2ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         := by rw [one_mul]
     _ = (a⁻¹ * a) * b := by rw [inv_mul_self]
     _ = a⁻¹ * (a * b) := by rw [mul_assoc]
     _ = a⁻¹ * (a * c) := by rw [h]
     _ = (a⁻¹ * a) * c := by rw [mul_assoc]
     _ = 1 * c         := by rw [inv_mul_self]
     _ = c             := by rw [one_mul]

-- 3ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         := by simp
     _ = (a⁻¹ * a) * b := by simp
     _ = a⁻¹ * (a * b) := by simp
     _ = a⁻¹ * (a * c) := by simp [h]
     _ = (a⁻¹ * a) * c := by simp
     _ = 1 * c         := by simp
     _ = c             := by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = a⁻¹ * (a * b) := by simp
     _ = a⁻¹ * (a * c) := by simp [h]
     _ = c             := by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
mul_left_cancel h

-- 5ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
by aesop

-- Lemas usados
-- ============

-- #check (inv_mul_self a : a⁻¹ * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_left_cancel : a * b = a * c → b = c)
-- #check (one_mul a : 1 * a = a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_cancelativa_en_grupos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Propiedad_cancelativa_en_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "b = 1 * b"                    by (simp only: left_neutral)
  also have "… = (inverse a * a) * b" by (simp only: left_inverse)
  also have "… = inverse a * (a * b)" by (simp only: assoc)
  also have "… = inverse a * (a * c)" by (simp only: ‹a * b = a * c›)
  also have "… = (inverse a * a) * c" by (simp only: assoc)
  also have "… = 1 * c"               by (simp only: left_inverse)
  also have "… = c"                   by (simp only: left_neutral)
  finally show "b = c"                by this
qed

(* 2ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "b = 1 * b"                    by simp
  also have "… = (inverse a * a) * b" by simp
  also have "… = inverse a * (a * b)" by (simp only: assoc)
  also have "… = inverse a * (a * c)" using ‹a * b = a * c› by simp
  also have "… = (inverse a * a) * c" by (simp only: assoc)
  also have "… = 1 * c"               by simp
  finally show "b = c"                by simp
qed

(* 3ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "b = (inverse a * a) * b"      by simp
  also have "… = inverse a * (a * b)" by (simp only: assoc)
  also have "… = inverse a * (a * c)" using ‹a * b = a * c› by simp
  also have "… = (inverse a * a) * c" by (simp only: assoc)
  finally show "b = c"                by simp
qed

(* 4ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "inverse a * (a * b) = inverse a * (a * c)"
    by (simp only: ‹a * b = a * c›)
  then have "(inverse a * a) * b = (inverse a * a) * c"
    by (simp only: assoc)
  then have "1 * b = 1 * c"
    by (simp only: left_inverse)
  then show "b = c"
    by (simp only: left_neutral)
qed

(* 5ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "inverse a * (a * b) = inverse a * (a * c)"
    by (simp only: ‹a * b = a * c›)
  then have "(inverse a * a) * b = (inverse a * a) * c"
    by (simp only: assoc)
  then have "1 * b = 1 * c"
    by (simp only: left_inverse)
  then show "b = c"
    by (simp only: left_neutral)
qed

(* 6ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
proof -
  have "inverse a * (a * b) = inverse a * (a * c)"
    using ‹a * b = a * c› by simp
  then have "(inverse a * a) * b = (inverse a * a) * c"
    by (simp only: assoc)
  then have "1 * b = 1 * c"
    by simp
  then show "b = c"
    by simp
qed

(* 7ª demostración *)

lemma
  assumes "a * b = a * c"
  shows   "b = c"
  using assms
  by (simp only: left_cancel)

end

end
</pre>
