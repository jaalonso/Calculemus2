---
title: Si G un grupo y a ∈ G, entonces (a⁻¹)⁻¹ = a
date: 2024-05-15 06:00:00 UTC+02:00
category: Grupos
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(G\\) un grupo y \\(a ∈ G\\), entonces
\\[(a⁻¹)⁻¹ = a\\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a : G}

example : (a⁻¹)⁻¹ = a :=
sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por la siguiente cadena de igualdades
\\begin{align}
   (a⁻¹)⁻¹ &= (a⁻¹)⁻¹·1          &&\\text{[porque \\(1\\) es neutro]} \\\\
           &= (a⁻¹)⁻¹·(a⁻¹·a)    &&\\text{[porque \\(a⁻¹\\) es el inverso de \\(a\\)]} \\\\
           &= ((a⁻¹)⁻¹·a⁻¹)·a    &&\\text{[por la asociativa]} \\\\
           &= 1·a                &&\\text{[porque \\((a⁻¹)⁻¹\\) es el inverso de \\(a⁻¹\\)]} \\\\
           &= a                  &&\\text{[porque \\(1\\) es neutro]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]
variable {a : G}

-- 1ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         := (mul_one (a⁻¹)⁻¹).symm
   _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := congrArg ((a⁻¹)⁻¹ * .) (inv_mul_self a).symm
   _ = ((a⁻¹)⁻¹ * a⁻¹) * a := (mul_assoc _ _ _).symm
   _ = 1 * a               := congrArg (. * a) (inv_mul_self a⁻¹)
   _ = a                   := one_mul a

-- 2ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         := by simp only [mul_one]
   _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := by simp only [inv_mul_self]
   _ = ((a⁻¹)⁻¹ * a⁻¹) * a := by simp only [mul_assoc]
   _ = 1 * a               := by simp only [inv_mul_self]
   _ = a                   := by simp only [one_mul]

-- 3ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         := by simp
   _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := by simp
   _ = ((a⁻¹)⁻¹ * a⁻¹) * a := by simp
   _ = 1 * a               := by simp
   _ = a                   := by simp

-- 4ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
by
  apply mul_eq_one_iff_inv_eq.mp
  -- ⊢ a⁻¹ * a = 1
  exact mul_left_inv a

-- 5ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
mul_eq_one_iff_inv_eq.mp (mul_left_inv a)

-- 6ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
inv_inv a

-- 7ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
by simp

-- Lemas usados
-- ============

-- variable (b c : G)
-- #check (inv_inv a : (a⁻¹)⁻¹ = a)
-- #check (inv_mul_self a : a⁻¹ * a = 1)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b)
-- #check (mul_left_inv a : a⁻¹  * a = 1)
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inverso_del_inverso_en_grupos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Inverso_del_inverso_en_grupos
imports Main
begin

context group
begin

(* 1ª demostración *)

lemma "inverse (inverse a) = a"
proof -
  have "inverse (inverse a) =
        (inverse (inverse a)) * 1"
    by (simp only: right_neutral)
  also have "… = inverse (inverse a) * (inverse a * a)"
    by (simp only: left_inverse)
  also have "… = (inverse (inverse a) * inverse a) * a"
    by (simp only: assoc)
  also have "… = 1 * a"
    by (simp only: left_inverse)
  also have "… = a"
    by (simp only: left_neutral)
  finally show "inverse (inverse a) = a"
    by this
qed

(* 2ª demostración *)

lemma "inverse (inverse a) = a"
proof -
  have "inverse (inverse a) =
        (inverse (inverse a)) * 1"                       by simp
  also have "… = inverse (inverse a) * (inverse a * a)" by simp
  also have "… = (inverse (inverse a) * inverse a) * a" by simp
  also have "… = 1 * a"                                 by simp
  finally show "inverse (inverse a) = a"                 by simp
qed

(* 3ª demostración *)

lemma "inverse (inverse a) = a"
proof (rule inverse_unique)
  show "inverse a * a = 1"
    by (simp only: left_inverse)
qed

(* 4ª demostración *)

lemma "inverse (inverse a) = a"
proof (rule inverse_unique)
  show "inverse a * a = 1" by simp
qed

(* 5ª demostración *)

lemma "inverse (inverse a) = a"
  by (rule inverse_unique) simp

(* 6ª demostración *)

lemma "inverse (inverse a) = a"
  by (simp only: inverse_inverse)

(* 7ª demostración *)

lemma "inverse (inverse a) = a"
  by simp

end

end
</pre>
