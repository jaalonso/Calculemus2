---
title: En los monoides, los inversos a la izquierda y a la derecha son iguales
date: 2024-05-03 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

Un [monoide](https://en.wikipedia.org/wiki/Monoid) es un conjunto junto con una operación binaria que es asociativa y tiene elemento neutro.

En Lean4, está definida la clase de los monoides (como `Monoid`) y sus propiedades características son

<pre lang="lean">
   mul_assoc : (a * b) * c = a * (b * c)
   one_mul :   1 * a = a
   mul_one :   a * 1 = a
</pre>

Demostrar que si \\(M\\) es un monoide, \\(a ∈ M\\), \\(b\\) es un inverso de \\(a\\) por la izquierda y \\(c\\) es un inverso de \\(a\\) por la derecha, entonces \\(b = c\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {M : Type} [Monoid M]
variable {a b c : M}

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por la siguiente cadena de igualdades
\\begin{align}
   b &= b * 1          &&\\text{[por mul_one]} \\\\
     &= b * (a * c)    &&\\text{[por hipótesis]} \\\\
     &= (b * a) * c    &&\\text{[por mul_assoc]} \\\\
     &= 1 * c          &&\\text{[por hipótesis]} \\\\
     &= c              &&\\text{[por one_mul]} \\\\
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Defs

variable {M : Type} [Monoid M]
variable {a b c : M}

-- 1ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b = b * 1       := (mul_one b).symm
     _ = b * (a * c) := congrArg (b * .) hac.symm
     _ = (b * a) * c := (mul_assoc b a c).symm
     _ = 1 * c       := congrArg (. * c) hba
     _ = c           := one_mul c

-- 2ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b  = b * 1       := by aesop
      _ = b * (a * c) := by aesop
      _ = (b * a) * c := (mul_assoc b a c).symm
      _ = 1 * c       := by aesop
      _ = c           := by aesop

-- 1ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by
  rw [←one_mul c]
  -- ⊢ b = 1 * c
  rw [←hba]
  -- ⊢ b = (b * a) * c
  rw [mul_assoc]
  -- ⊢ b = b * (a * c)
  rw [hac]
  -- ⊢ b = b * 1
  rw [mul_one b]

-- 2ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

-- 5ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
left_inv_eq_right_inv hba hac

-- Lemas usados
-- ============

-- #check (left_inv_eq_right_inv : b * a = 1 → a * c = 1 → b = c)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales
imports Main
begin

context monoid
begin

(* 1ª demostración *)

lemma
  assumes "b * a = 1"
          "a * c = 1"
  shows   "b = c"
proof -
  have      "b  = b * 1"      by (simp only: right_neutral)
  also have "… = b * (a * c)" by (simp only: ‹a * c = 1›)
  also have "… = (b * a) * c" by (simp only: assoc)
  also have "… = 1 * c"       by (simp only: ‹b * a = 1›)
  also have "… = c"           by (simp only: left_neutral)
  finally show "b = c"        by this
qed

(* 2ª demostración *)

lemma
  assumes "b * a = 1"
          "a * c = 1"
  shows   "b = c"
proof -
  have      "b  = b * 1"      by simp
  also have "… = b * (a * c)" using ‹a * c = 1› by simp
  also have "… = (b * a) * c" by (simp add: assoc)
  also have "… = 1 * c"       using ‹b * a = 1› by simp
  also have "… = c"           by simp
  finally show "b = c"        by this
qed

(* 3ª demostración *)

lemma
  assumes "b * a = 1"
          "a * c = 1"
  shows   "b = c"
  using assms
  by (metis assoc left_neutral right_neutral)

end

end
</pre>
