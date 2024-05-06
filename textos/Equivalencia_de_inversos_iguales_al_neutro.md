---
title: Equivalencia de inversos iguales al neutro
date: 2024-05-07 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

Sea \\(M\\) un monoide y \\(a, b ∈ M\\) tales que \\(ab = 1\\). Demostrar con Lean4 que \\(a = 1\\) si y sólo si \\(b = 1\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [Monoid M]
variable {a b : M}

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Demostraremos las dos implicaciones.

(⟹) Supongamos que \\(a = 1\\). Entonces,
\\begin{align}
   b &= 1·b    &&\\text{[por neutro por la izquierda]} \\\\
     &= a·b    &&\\text{[por supuesto]} \\\\
     &= 1      &&\\text{[por hipótesis]}
\\end{align}

(⟸) Supongamos que \\(b = 1\\). Entonces,
\\begin{align}
   a &= a·1    &&\\text{[por neutro por la derecha]} \\\\
     &= a·b    &&\\text{[por supuesto]} \\\\
     &= 1      &&\\text{[por hipótesis]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Basic

variable {M : Type} [Monoid M]
variable {a b : M}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by
  constructor
  . -- ⊢ a = 1 → b = 1
    intro a1
    -- a1 : a = 1
    -- ⊢ b = 1
    calc b = 1 * b := (one_mul b).symm
         _ = a * b := congrArg (. * b) a1.symm
         _ = 1     := h
  . -- ⊢ b = 1 → a = 1
    intro b1
    -- b1 : b = 1
    -- ⊢ a = 1
    calc a = a * 1 := (mul_one a).symm
         _ = a * b := congrArg (a * .) b1.symm
         _ = 1     := h

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by
  constructor
  . -- ⊢ a = 1 → b = 1
    intro a1
    -- a1 : a = 1
    -- ⊢ b = 1
    rw [a1] at h
    -- h : 1 * b = 1
    rw [one_mul] at h
    -- h : b = 1
    exact h
  . -- ⊢ b = 1 → a = 1
    intro b1
    -- b1 : b = 1
    -- ⊢ a = 1
    rw [b1] at h
    -- h : a * 1 = 1
    rw [mul_one] at h
    -- h : a = 1
    exact h

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by
  constructor
  . -- ⊢ a = 1 → b = 1
    rintro rfl
    -- h : 1 * b = 1
    simpa using h
  . -- ⊢ b = 1 → a = 1
    rintro rfl
    -- h : a * 1 = 1
    simpa using h

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by constructor <;> (rintro rfl; simpa using h)

-- 5ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
eq_one_iff_eq_one_of_mul_eq_one h

-- Lemas usados
-- ============

-- #check (eq_one_iff_eq_one_of_mul_eq_one : a * b = 1 → (a = 1 ↔ b = 1))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Equivalencia_de_inversos_iguales_al_neutro.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Equivalencia_de_inversos_iguales_al_neutro
imports Main
begin

context monoid
begin

(* 1ª demostración *)

lemma
  assumes "a ❙* b = ❙1"
  shows   "a = ❙1 ⟷ b = ❙1"
proof (rule iffI)
  assume "a = ❙1"
  have "b = ❙1 ❙* b"       by (simp only: left_neutral)
  also have "… = a ❙* b" by (simp only: ‹a = ❙1›)
  also have "… = ❙1"     by (simp only: ‹a ❙* b = ❙1›)
  finally show "b = ❙1"   by this
next
  assume "b = ❙1"
  have "a = a ❙* ❙1"       by (simp only: right_neutral)
  also have "… = a ❙* b" by (simp only: ‹b = ❙1›)
  also have "… = ❙1"     by (simp only: ‹a ❙* b = ❙1›)
  finally show "a = ❙1"   by this
qed

(* 2ª demostración *)

lemma
  assumes "a ❙* b = ❙1"
  shows   "a = ❙1 ⟷ b = ❙1"
proof
  assume "a = ❙1"
  have "b = ❙1 ❙* b"       by simp
  also have "… = a ❙* b" using ‹a = ❙1› by simp
  also have "… = ❙1"     using ‹a ❙* b = ❙1› by simp
  finally show "b = ❙1"   .
next
  assume "b = ❙1"
  have "a = a ❙* ❙1"       by simp
  also have "… = a ❙* b" using ‹b = ❙1› by simp
  also have "… = ❙1"     using ‹a ❙* b = ❙1› by simp
  finally show "a = ❙1"   .
qed

(* 3ª demostración *)

lemma
  assumes "a ❙* b = ❙1"
  shows   "a = ❙1 ⟷ b = ❙1"
  by (metis assms left_neutral right_neutral)

end

end
</pre>
