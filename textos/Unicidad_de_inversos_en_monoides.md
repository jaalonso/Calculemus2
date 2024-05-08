---
title: Unicidad de inversos en monoides
date: 2024-05-08 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(M\\) es un monoide conmutativo y \\(x, y, z ∈ M\\) tales que \\(x·y = 1\\) y \\(x·z = 1\\), entonces \\(y = z\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [CommMonoid M]
variable {x y z : M}

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por la siguiente cadena de igualdades
\\begin{align}
   y &= 1·y          &&\\text{[por neutro a la izquierda]} \\\\
     &= (x·z)·y      &&\\text{[por hipótesis]} \\\\
     &= (z·x)·y      &&\\text{[por la conmutativa]} \\\\
     &= z·(x·y)      &&\\text{[por la asociativa]} \\\\
     &= z·1          &&\\text{[por hipótesis]} \\\\
     &= z            &&\\text{[por neutro a la derecha]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [CommMonoid M]
variable {x y z : M}

-- 1ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       := (one_mul y).symm
     _ = (x * z) * y := congrArg (. * y) hz.symm
     _ = (z * x) * y := congrArg (. * y) (mul_comm x z)
     _ = z * (x * y) := mul_assoc z x y
     _ = z * 1       := congrArg (z * .) hy
     _ = z           := mul_one z

-- 2ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y     := by simp only [one_mul]
   _ = (x * z) * y := by simp only [hz]
   _ = (z * x) * y := by simp only [mul_comm]
   _ = z * (x * y) := by simp only [mul_assoc]
   _ = z * 1       := by simp only [hy]
   _ = z           := by simp only [mul_one]

-- 3ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y     := by simp
   _ = (x * z) * y := by simp [hz]
   _ = (z * x) * y := by simp [mul_comm]
   _ = z * (x * y) := by simp [mul_assoc]
   _ = z * 1       := by simp [hy]
   _ = z           := by simp

-- 4ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
by
  apply left_inv_eq_right_inv _ hz
  -- ⊢ y * x = 1
  rw [mul_comm]
  -- ⊢ x * y = 1
  exact hy

-- 5ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
inv_unique hy hz

-- Lemas usados
-- ============

-- #check (inv_unique : x * y = 1 → x * z = 1 → y = z)
-- #check (left_inv_eq_right_inv : y * x = 1 → x * z = 1 → y = z)
-- #check (mul_assoc x y z : (x * y) * z = x * (y * z))
-- #check (mul_comm x y : x * y = y * x)
-- #check (mul_one x : x * 1 = x)
-- #check (one_mul x : 1 * x = x)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Unicidad_de_inversos_en_monoides.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Unicidad_de_inversos_en_monoides
imports Main
begin

context comm_monoid
begin

(* 1ª demostración *)

lemma
  assumes "x * y = 1"
          "x * z = 1"
  shows "y = z"
proof -
  have "y = 1 * y"            by (simp only: left_neutral)
  also have "… = (x * z) * y" by (simp only: ‹x * z = 1›)
  also have "… = (z * x) * y" by (simp only: commute)
  also have "… = z * (x * y)" by (simp only: assoc)
  also have "… = z * 1"       by (simp only: ‹x * y = 1›)
  also have "… = z"           by (simp only: right_neutral)
  finally show "y = z"        by this
qed

(* 2ª demostración *)

lemma
  assumes "x * y = 1"
          "x * z = 1"
  shows "y = z"
proof -
  have "y = 1 * y"            by simp
  also have "… = (x * z) * y" using assms(2) by simp
  also have "… = (z * x) * y" by simp
  also have "… = z * (x * y)" by simp
  also have "… = z * 1"       using assms(1) by simp
  also have "… = z"           by simp
  finally show "y = z"        by this
qed

(* 3ª demostración *)

lemma
  assumes "x * y = 1"
          "x * z = 1"
  shows "y = z"
  using assms
  by auto

end

end
</pre>
