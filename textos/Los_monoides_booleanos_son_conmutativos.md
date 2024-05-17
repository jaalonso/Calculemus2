---
title: Los monoides booleanos son conmutativos
date: 2024-05-20 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

Un monoide es un conjunto junto con una operación binaria que es asociativa y tiene elemento neutro.

Un monoide \\(M\\) es booleano si
\\[ (∀ x ∈ M)[x·x = 1] \\]
y es conmutativo si
\\[ (∀ x, y ∈ M)[x·y = y·x] \\]

En Lean4, está definida la clase de los monoides (como `Monoid`) y sus propiedades características son
<pre lang="lean">
   mul_assoc : (a * b) * c = a * (b * c)
   one_mul :   1 * a = a
   mul_one :   a * 1 = a
</pre>

Demostrar con Lean4 que los monoides booleanos son conmutativos.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [Monoid M]

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(a, b ∈ M\\). Se verifica la siguiente cadena de igualdades
\\begin{align}
   a·b &= (a·b)·1               &&\\text{[por mul_one]} \\\\
       &= (a·b)·(a·a)           &&\\text{[por hipótesis, \\(a·a = 1\\)]} \\\\
       &= ((a·b)·a)·a           &&\\text{[por mul_assoc]} \\\\
       &= (a·(b·a))·a           &&\\text{[por mul_assoc]} \\\\
       &= (1·(a·(b·a)))·a       &&\\text{[por one_mul]} \\\\
       &= ((b·b)·(a·(b·a)))·a   &&\\text{[por hipótesis, \\(b·b = 1\\)]} \\\\
       &= (b·(b·(a·(b·a))))·a   &&\\text{[por mul_assoc]} \\\\
       &= (b·((b·a)·(b·a)))·a   &&\\text{[por mul_assoc]} \\\\
       &= (b·1)·a               &&\\text{[por hipótesis, \\((b·a)·(b·a) = 1\\)]} \\\\
       &= b·a                   &&\\text{[por mul_one]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [Monoid M]

-- 1ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1
         := (mul_one (a * b)).symm
     _ = (a * b) * (a * a)
         := congrArg ((a*b) * .) (h a).symm
     _ = ((a * b) * a) * a
         := (mul_assoc (a*b) a a).symm
     _ = (a * (b * a)) * a
         := congrArg (. * a) (mul_assoc a b a)
     _ = (1 * (a * (b * a))) * a
         := congrArg (. * a) (one_mul (a*(b*a))).symm
     _ = ((b * b) * (a * (b * a))) * a
         := congrArg (. * a) (congrArg (. * (a*(b*a))) (h b).symm)
     _ = (b * (b * (a * (b * a)))) * a
         := congrArg (. * a) (mul_assoc b b (a*(b*a)))
     _ = (b * ((b * a) * (b * a))) * a
         := congrArg (. * a) (congrArg (b * .) (mul_assoc b a (b*a)).symm)
     _ = (b * 1) * a
         := congrArg (. * a) (congrArg (b * .) (h (b*a)))
     _ = b * a
         := congrArg (. * a) (mul_one b)

-- 2ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1                   := by simp only [mul_one]
     _ = (a * b) * (a * a)             := by simp only [h a]
     _ = ((a * b) * a) * a             := by simp only [mul_assoc]
     _ = (a * (b * a)) * a             := by simp only [mul_assoc]
     _ = (1 * (a * (b * a))) * a       := by simp only [one_mul]
     _ = ((b * b) * (a * (b * a))) * a := by simp only [h b]
     _ = (b * (b * (a * (b * a)))) * a := by simp only [mul_assoc]
     _ = (b * ((b * a) * (b * a))) * a := by simp only [mul_assoc]
     _ = (b * 1) * a                   := by simp only [h (b*a)]
     _ = b * a                         := by simp only [mul_one]

-- 3ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1                   := by simp only [mul_one]
     _ = (a * b) * (a * a)             := by simp only [h a]
     _ = (a * (b * a)) * a             := by simp only [mul_assoc]
     _ = (1 * (a * (b * a))) * a       := by simp only [one_mul]
     _ = ((b * b) * (a * (b * a))) * a := by simp only [h b]
     _ = (b * ((b * a) * (b * a))) * a := by simp only [mul_assoc]
     _ = (b * 1) * a                   := by simp only [h (b*a)]
     _ = b * a                         := by simp only [mul_one]

-- 4ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1                   := by simp
     _ = (a * b) * (a * a)             := by simp only [h a]
     _ = (a * (b * a)) * a             := by simp only [mul_assoc]
     _ = (1 * (a * (b * a))) * a       := by simp
     _ = ((b * b) * (a * (b * a))) * a := by simp only [h b]
     _ = (b * ((b * a) * (b * a))) * a := by simp only [mul_assoc]
     _ = (b * 1) * a                   := by simp only [h (b*a)]
     _ = b * a                         := by simp

-- Lemas usados
-- ============

-- variable (a b c : M)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Los_monoides_booleanos_son_conmutativos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Los_monoides_booleanos_son_conmutativos
imports Main
begin

context monoid
begin

(* 1ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
proof (rule allI)+
  fix a b
  have "a * b = (a * b) * 1"
    by (simp only: right_neutral)
  also have "… = (a * b) * (a * a)"
    by (simp only: assms)
  also have "… = ((a * b) * a) * a"
    by (simp only: assoc)
  also have "… = (a * (b * a)) * a"
    by (simp only: assoc)
  also have "… = (1 * (a * (b * a))) * a"
    by (simp only: left_neutral)
  also have "… = ((b * b) * (a * (b * a))) * a"
    by (simp only: assms)
  also have "… = (b * (b * (a * (b * a)))) * a"
    by (simp only: assoc)
  also have "… = (b * ((b * a) * (b * a))) * a"
    by (simp only: assoc)
  also have "… = (b * 1) * a"
    by (simp only: assms)
  also have "… = b * a"
    by (simp only: right_neutral)
  finally show "a * b = b * a"
    by this
qed

(* 2ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
proof (rule allI)+
  fix a b
  have "a * b = (a * b) * 1"                    by simp
  also have "… = (a * b) * (a * a)"             by (simp add: assms)
  also have "… = ((a * b) * a) * a"             by (simp add: assoc)
  also have "… = (a * (b * a)) * a"             by (simp add: assoc)
  also have "… = (1 * (a * (b * a))) * a"       by simp
  also have "… = ((b * b) * (a * (b * a))) * a" by (simp add: assms)
  also have "… = (b * (b * (a * (b * a)))) * a" by (simp add: assoc)
  also have "… = (b * ((b * a) * (b * a))) * a" by (simp add: assoc)
  also have "… = (b * 1) * a"                   by (simp add: assms)
  also have "… = b * a"                         by simp
  finally show "a * b = b * a"                  by this
qed

(* 3ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
proof (rule allI)+
  fix a b
  have "a * b = (a * b) * (a * a)"              by (simp add: assms)
  also have "… = (a * (b * a)) * a"             by (simp add: assoc)
  also have "… = ((b * b) * (a * (b * a))) * a" by (simp add: assms)
  also have "… = (b * ((b * a) * (b * a))) * a" by (simp add: assoc)
  also have "… = (b * 1) * a"                   by (simp add: assms)
  finally show "a * b = b * a"                  by simp
qed

(* 4ª demostración *)

lemma
  assumes "∀ x. x * x = 1"
  shows   "∀ x y. x * y = y * x"
  by (metis assms assoc right_neutral)

end

end
</pre>
