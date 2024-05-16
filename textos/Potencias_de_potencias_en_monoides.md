---
title: Si M es un monoide, a ∈ M y m, n ∈ ℕ, entonces a^(m·n) = (a^m)^n
date: 2024-05-17 06:00:00 UTC+02:00
category: Monoides
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(M\\) es un monoide, \\(a ∈ M\\) y \\(m, n ∈ ℕ\\), entonces
\\[ a^{m·n} = (a^m)^n \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Algebra.GroupPower.Basic
open Nat

variable {M : Type} [Monoid M]
variable (a : M)
variable (m n : ℕ)

example : a^(m * n) = (a^m)^n :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por inducción en \\(n\\).

**Caso base**: Supongamos que \\(n = 0\\). Entonces,
\\begin{align}
   a^{m·0} &= a^0       \\\\
           &= 1         &&\\text{[por pow_zero]} \\\\
           &= (a^m)^0   &&\\text{[por pow_zero]}
\\end{align}

Paso de indución: Supogamos que se verifica para \\(n\\); es decir,
\\[ a^{m·n} = (a^m)^n \\tag{HI} \\]
Entonces,
\\begin{align}
   a^{m·(n+1)} &= a^{m·n + m}    \\\\
               &= a^{m·n}·a^m    \\\\
               &= (a^m)^n·a^m    &&\\text{[por HI]} \\\\
               &= (a^m)^{n+1}    &&\\text{[por pow_succ']}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Algebra.GroupPower.Basic
open Nat

variable {M : Type} [Monoid M]
variable (a : M)
variable (m n : ℕ)

-- 1ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . calc a^(m * 0)
         = a^0             := congrArg (a ^ .) (Nat.mul_zero m)
       _ = 1               := pow_zero a
       _ = (a^m)^0         := (pow_zero (a^m)).symm
  . calc a^(m * succ n)
         = a^(m * n + m)   := congrArg (a ^ .) (Nat.mul_succ m n)
       _ = a^(m * n) * a^m := pow_add a (m * n) m
       _ = (a^m)^n * a^m   := congrArg (. * a^m) HI
       _ = (a^m)^(succ n)  := (pow_succ' (a^m) n).symm

-- 2ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . calc a^(m * 0)
         = a^0             := by simp only [Nat.mul_zero]
       _ = 1               := by simp only [_root_.pow_zero]
       _ = (a^m)^0         := by simp only [_root_.pow_zero]
  . calc a^(m * succ n)
         = a^(m * n + m)   := by simp only [Nat.mul_succ]
       _ = a^(m * n) * a^m := by simp only [pow_add]
       _ = (a^m)^n * a^m   := by simp only [HI]
       _ = (a^m)^succ n    := by simp only [_root_.pow_succ']

-- 3ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . calc a^(m * 0)
         = a^0             := by simp [Nat.mul_zero]
       _ = 1               := by simp
       _ = (a^m)^0         := by simp
  . calc a^(m * succ n)
         = a^(m * n + m)   := by simp [Nat.mul_succ]
       _ = a^(m * n) * a^m := by simp [pow_add]
       _ = (a^m)^n * a^m   := by simp [HI]
       _ = (a^m)^succ n    := by simp [_root_.pow_succ']

-- 4ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . simp [Nat.mul_zero]
  . simp [Nat.mul_succ,
          pow_add,
          HI,
          _root_.pow_succ']

-- 5ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . -- ⊢ a ^ (m * zero) = (a ^ m) ^ zero
    rw [Nat.mul_zero]
    -- ⊢ a ^ 0 = (a ^ m) ^ zero
    rw [_root_.pow_zero]
    -- ⊢ 1 = (a ^ m) ^ zero
    rw [_root_.pow_zero]
  . -- ⊢ a ^ (m * succ n) = (a ^ m) ^ succ n
    rw [Nat.mul_succ]
    -- ⊢ a ^ (m * n + m) = (a ^ m) ^ succ n
    rw [pow_add]
    -- ⊢ a ^ (m * n) * a ^ m = (a ^ m) ^ succ n
    rw [HI]
    -- ⊢ (a ^ m) ^ n * a ^ m = (a ^ m) ^ succ n
    rw [_root_.pow_succ']

-- 6ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
by
  induction' n with n HI
  . rw [Nat.mul_zero, _root_.pow_zero, _root_.pow_zero]
  . rw [Nat.mul_succ, pow_add, HI, _root_.pow_succ']

-- 7ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
pow_mul a m n

-- Lemas usados
-- ============

-- #check (Nat.mul_succ n m : n * succ m = n * m + n)
-- #check (Nat.mul_zero m : m * 0 = 0)
-- #check (pow_add a m n : a ^ (m + n) = a ^ m * a ^ n)
-- #check (pow_mul a m n : a ^ (m * n) = (a ^ m) ^ n)
-- #check (pow_succ' a n : a ^ (n + 1) = a ^ n * a)
-- #check (pow_zero a : a ^ 0 = 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Potencias_de_potencias_en_monoides.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Potencias_de_potencias_en_monoides
imports Main
begin

context monoid_mult
begin

(* 1ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  have "a ^ (m * 0) = a ^ 0"
    by (simp only: mult_0_right)
  also have "… = 1"
    by (simp only: power_0)
  also have "… = (a ^ m) ^ 0"
    by (simp only: power_0)
  finally show "a ^ (m * 0) = (a ^ m) ^ 0"
    by this
next
  fix n
  assume HI : "a ^ (m * n) = (a ^ m) ^ n"
  have "a ^ (m * Suc n) = a ^ (m + m * n)"
    by (simp only: mult_Suc_right)
  also have "… = a ^ m * a ^ (m * n)"
    by (simp only: power_add)
  also have "… = a ^ m * (a ^ m) ^ n"
    by (simp only: HI)
  also have "… = (a ^ m) ^ Suc n"
    by (simp only: power_Suc)
  finally show "a ^ (m * Suc n) = (a ^ m) ^ Suc n"
    by this
qed

(* 2ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  have "a ^ (m * 0) = a ^ 0"               by simp
  also have "… = 1"                        by simp
  also have "… = (a ^ m) ^ 0"              by simp
  finally show "a ^ (m * 0) = (a ^ m) ^ 0" .
next
  fix n
  assume HI : "a ^ (m * n) = (a ^ m) ^ n"
  have "a ^ (m * Suc n) = a ^ (m + m * n)" by simp
  also have "… = a ^ m * a ^ (m * n)"      by (simp add: power_add)
  also have "… = a ^ m * (a ^ m) ^ n"      using HI by simp
  also have "… = (a ^ m) ^ Suc n"          by simp
  finally show "a ^ (m * Suc n) =
                (a ^ m) ^ Suc n"           .
qed

(* 3ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: power_add)
qed

(* 4ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
  by (induct n) (simp_all add: power_add)

(* 5ª demostración *)

lemma "a^(m * n) = (a^m)^n"
  by (simp only: power_mult)

end

end
</pre>
