---
title: Caracterización de producto igual al primer factor
date: 2024-05-09 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

Un monoide cancelativo por la izquierda es un monoide \\(M\\) que cumple la propiedad cancelativa por la izquierda; es decir, para todo \\(a, b ∈ M\\)
\\[ a·b = a·c ↔ b = c \\]

En Lean4 la clase de los monoides cancelativos por la izquierda es `LeftCancelMonoid` y la propiedad cancelativa por la izquierda es
<pre lang="lean">
   mul_left_cancel : a * b = a * c → b = c
</pre>

Demostrar con Lean4 que si \\(M\\) es un monoide cancelativo por la izquierda y \\(a, b ∈ M\\), entonces
\\[ a·b = a ↔ b = 1 \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [LeftCancelMonoid M]
variable {a b : M}

example : a * b = a ↔ b = 1 :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Demostraremos las dos implicaciones.

(⟹) Supongamos que
\\[ a·b = a  \\]
Por la propiedad del neutro por la derecha tenemos
\\[ a·1 = a \\]
Por tanto,
\\[ a·b = a·1 \\]
y, por la propiedad cancelativa,
\\[ b = 1 \\]

(⟸) Supongamos que \\(b = 1\\). Entonces,
\\begin{align}
   a·b &= a·1    \\\\
       &= a      &&\\text{[por el neutro por la derecha]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [LeftCancelMonoid M]
variable {a b : M}

-- 1ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
by
  constructor
  . -- ⊢ a * b = a → b = 1
    intro h
    -- h : a * b = a
    -- ⊢ b = 1
    have h1 : a * b = a * 1 := by
      calc a * b = a     := by exact h
               _ = a * 1 := (mul_one a).symm
    exact mul_left_cancel h1
  . -- ⊢ b = 1 → a * b = a
    intro h
    -- h : b = 1
    -- ⊢ a * b = a
    rw [h]
    -- ⊢ a * 1 = a
    exact mul_one a

-- 2ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
calc a * b = a
     ↔ a * b = a * 1 := by rw [mul_one]
   _ ↔ b = 1         := mul_left_cancel_iff

-- 3ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
mul_right_eq_self

-- 4ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
by aesop

-- Lemas usados
-- ============

-- variable (c : M)
-- #check (mul_left_cancel : a * b = a * c → b = c)
-- #check (mul_one a : a * 1 = a)
-- #check (mul_right_eq_self : a * b = a ↔ b = 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Caracterizacion_de_producto_igual_al_primer_factor.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Caracterizacion_de_producto_igual_al_primer_factor
imports Main
begin

context cancel_comm_monoid_add
begin

(* 1ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof (rule iffI)
  assume "a + b = a"
  then have "a + b = a + 0"     by (simp only: add_0_right)
  then show "b = 0"             by (simp only: add_left_cancel)
next
  assume "b = 0"
  have "a + 0 = a"              by (simp only: add_0_right)
  with ‹b = 0› show "a + b = a" by (rule ssubst)
qed

(* 2ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof
  assume "a + b = a"
  then have "a + b = a + 0" by simp
  then show "b = 0"         by simp
next
  assume "b = 0"
  have "a + 0 = a"          by simp
  then show "a + b = a"     using ‹b = 0› by simp
qed

(* 3ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof -
  have "(a + b = a) ⟷ (a + b = a + 0)" by (simp only: add_0_right)
  also have "… ⟷ (b = 0)"             by (simp only: add_left_cancel)
  finally show "a + b = a ⟷ b = 0"     by this
qed

(* 4ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof -
  have "(a + b = a) ⟷ (a + b = a + 0)" by simp
  also have "… ⟷ (b = 0)"             by simp
  finally show "a + b = a ⟷ b = 0"     .
qed

(* 5ª demostración *)

lemma "a + b = a ⟷ b = 0"
  by (simp only: add_cancel_left_right)

(* 6ª demostración *)

lemma "a + b = a ⟷ b = 0"
  by auto

end

end
</pre>
