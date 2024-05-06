---
title: Producto de potencias de la misma base en monoides
date: 2024-05-06 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la potencia con exponentes naturales. En Lean la potencia x^n se se caracteriza por los siguientes lemas:

<pre lang="lean">
   pow_zero : x^0 = 1
   pow_succ : x^(succ n) = x * x^n
</pre>

Demostrar con Lean4 que si \\(M\\) es un monoide, \\(x ∈ M\\) y \\(m, n ∈ ℕ\\), entonces
\\[ x^{m + n} = x^m  x^n \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
open Nat

variable {M : Type} [Monoid M]
variable (x : M)
variable (m n : ℕ)

example :
  x^(m + n) = x^m * x^n :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por inducción en \\(m\\).

**Base**:
\\begin{align}
   x^{0 + n} &= x^n        \\\\
             &= 1 · x^n    \\\\
             &= x^0 · x^n  &&\\text{[por pow_zero]}
\\end{align}

**Paso**: Supongamos que
\\[ x^{m + n} = x^m x^n \\tag{HI} \\]
Entonces
\\begin{align}
   x^{(m+1) + n} &= x^{(m + n) + 1}  \\\\
                 &= x · x^{m + n}    &&\\text{[por pow_succ]} \\\\
                 &= x · (x^m · x^n)  &&\\text{[por HI]} \\\\
                 &= (x · x^m) · x^n  \\\\
                 &= x^{m+1} · x^n    &&\\text{[por pow_succ]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
open Nat

variable {M : Type} [Monoid M]
variable (x : M)
variable (m n : ℕ)

-- 1ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
by
  induction' m with m HI
  . calc x^(0 + n)
       = x^n               := congrArg (x ^ .) (Nat.zero_add n)
     _ = 1 * x^n           := (Monoid.one_mul (x^n)).symm
     _ = x^0 * x^n         := congrArg (. * (x^n)) (pow_zero x).symm
  . calc x^(succ m + n)
       = x^succ (m + n)    := congrArg (x ^.) (succ_add m n)
     _ = x * x^(m + n)     := pow_succ x (m + n)
     _ = x * (x^m * x^n)   := congrArg (x * .) HI
     _ = (x * x^m) * x^n   := (mul_assoc x (x^m) (x^n)).symm
     _ = x^succ m * x^n    := congrArg (. * x^n) (pow_succ x m).symm

-- 2ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
by
  induction' m with m HI
  . calc x^(0 + n)
       = x^n             := by simp only [Nat.zero_add]
     _ = 1 * x^n         := by simp only [Monoid.one_mul]
     _ = x^0 * x^n       := by simp only [_root_.pow_zero]
  . calc x^(succ m + n)
       = x^succ (m + n)  := by simp only [succ_add]
     _ = x * x^(m + n)   := by simp only [_root_.pow_succ]
     _ = x * (x^m * x^n) := by simp only [HI]
     _ = (x * x^m) * x^n := (mul_assoc x (x^m) (x^n)).symm
     _ = x^succ m * x^n  := by simp only [_root_.pow_succ]

-- 3ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
by
  induction' m with m HI
  . calc x^(0 + n)
       = x^n             := by simp [Nat.zero_add]
     _ = 1 * x^n         := by simp
     _ = x^0 * x^n       := by simp
  . calc x^(succ m + n)
       = x^succ (m + n)  := by simp [succ_add]
     _ = x * x^(m + n)   := by simp [_root_.pow_succ]
     _ = x * (x^m * x^n) := by simp [HI]
     _ = (x * x^m) * x^n := (mul_assoc x (x^m) (x^n)).symm
     _ = x^succ m * x^n  := by simp [_root_.pow_succ]

-- 4ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
pow_add x m n

-- Lemas usados
-- ============

-- variable (y z : M)
-- #check (Monoid.one_mul x : 1 * x = x)
-- #check (Nat.zero_add n : 0 + n = n)
-- #check (mul_assoc x y z : (x * y) * z = x * (y * z))
-- #check (pow_add x m n : x^(m + n) = x^m * x^n)
-- #check (pow_succ x n : x ^ succ n = x * x ^ n)
-- #check (pow_zero x : x ^ 0 = 1)
-- #check (succ_add n m : succ n + m = succ (n + m))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_de_potencias_de_la_misma_base_en_monoides.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Producto_de_potencias_de_la_misma_base_en_monoides
imports Main
begin

context monoid_mult
begin

(* 1ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  have "x ^ (0 + n) = x ^ n"                 by (simp only: add_0)
  also have "… = 1 * x ^ n"                 by (simp only: mult_1_left)
  also have "… = x ^ 0 * x ^ n"             by (simp only: power_0)
  finally show "x ^ (0 + n) = x ^ 0 * x ^ n"
    by this
next
  fix m
  assume HI : "x ^ (m + n) = x ^ m * x ^ n"
  have "x ^ (Suc m + n) = x ^ Suc (m + n)"    by (simp only: add_Suc)
  also have "… = x *  x ^ (m + n)"           by (simp only: power_Suc)
  also have "… = x *  (x ^ m * x ^ n)"       by (simp only: HI)
  also have "… = (x *  x ^ m) * x ^ n"       by (simp only: mult_assoc)
  also have "… = x ^ Suc m * x ^ n"          by (simp only: power_Suc)
  finally show "x ^ (Suc m + n) = x ^ Suc m * x ^ n"
    by this
qed

(* 2ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  have "x ^ (0 + n) = x ^ n"                  by simp
  also have "… = 1 * x ^ n"                  by simp
  also have "… = x ^ 0 * x ^ n"              by simp
  finally show "x ^ (0 + n) = x ^ 0 * x ^ n"
    by this
next
  fix m
  assume HI : "x ^ (m + n) = x ^ m * x ^ n"
  have "x ^ (Suc m + n) = x ^ Suc (m + n)"    by simp
  also have "… = x *  x ^ (m + n)"           by simp
  also have "… = x *  (x ^ m * x ^ n)"       using HI by simp
  also have "… = (x *  x ^ m) * x ^ n"       by (simp add: mult_assoc)
  also have "… = x ^ Suc m * x ^ n"          by simp
  finally show "x ^ (Suc m + n) = x ^ Suc m * x ^ n"
    by this
qed

(* 3ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  then show ?case
    by (simp add: algebra_simps)
qed

(* 4ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
  by (induct m) (simp_all add: algebra_simps)

(* 5ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
  by (simp only: power_add)

end

end
</pre>
