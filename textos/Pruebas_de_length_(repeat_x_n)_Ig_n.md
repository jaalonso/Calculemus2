---
title: Pruebas de length (replicate n x) = n
date: 2024-07-29 06:00:00 UTC+02:00
category: Listas
has_math: true
---

[mathjax]

En Lean4 están definidas las funciones length y replicate tales que

+ (length xs) es la longitud de la lista xs. Por ejemplo,
<pre lang="lean">
     length [1,2,5,2] = 4
</pre>
+ (replicate n x) es la lista que tiene el elemento x n veces. Por ejemplo,
<pre lang="lean">
     replicate 3 7 = [7, 7, 7]
</pre>

Demostrar que
<pre lang="lean">
   length (replicate n x) = n
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.List.Basic
open Nat
open List

variable {α : Type}
variable (x : α)
variable (n : ℕ)

example :
  length (replicate n x) = n :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por inducción en n

**Caso base**:
\\begin{align}
   length (replicate 0 x) &= length [] \\\\
                          &= 0
\\end{align}

**Paso de inducción**: Se supone la hipótesis de inducción
\\[ length (replicate n x) = n \\tag{HI} \\]
Entonces,
\\begin{align}
   length (replicate (n+1) x)       \\\\
   & = length (x :: replicate n x)  \\\\
   & = length (replicate n x) + 1   \\\\
   & = n + 1                        &&\\text{[por la HI]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.List.Basic
open Nat
open List

variable {α : Type}
variable (x : α)
variable (n : ℕ)

-- 1ª demostración
-- ===============

example :
  length (replicate n x) = n :=
by
  induction' n with n HI
  . calc length (replicate 0 x)
          = length []                   := rfl
        _ = 0                           := length_nil
  . calc length (replicate (n+1) x)
         = length (x :: replicate n x)  := congr_arg length (replicate_succ x n)
       _ = length (replicate n x) + 1   := length_cons x (replicate n x)
       _ = n + 1                        := congrArg (. + 1) HI

-- 2ª demostración
-- ===============

example :
  length (replicate n x) = n :=
by
  induction' n with n HI
  . calc length (replicate 0 x)
          = length []                   := rfl
        _ = 0                           := rfl
  . calc length (replicate (n+1) x)
         = length (x :: replicate n x)  := rfl
       _ = length (replicate n x) + 1   := rfl
       _ = n + 1                        := by rw [HI]

-- 3ª demostración
-- ===============

example : length (replicate n x) = n :=
by
  induction' n with n HI
  . rfl
  . dsimp
    rw [HI]

-- 4ª demostración
-- ===============

example : length (replicate n x) = n :=
by
  induction' n with n HI
  . simp
  . simp [HI]

-- 5ª demostración
-- ===============

example : length (replicate n x) = n :=
by induction' n <;> simp [*]

-- 6ª demostración
-- ===============

example : length (replicate n x) = n :=
length_replicate n x

-- 7ª demostración
-- ===============

example : length (replicate n x) = n :=
by simp

-- 8ª demostración
-- ===============

lemma length_replicate_1 n (x : α) :
  length (replicate n x) = n :=
by induction n with
  | zero => calc
    length (replicate 0 x)
      = length ([] : List α)         := by simp only [replicate_zero]
    _ = 0                            := length_nil
  | succ n HI => calc
    length (replicate  (n + 1) x)
      = length (x :: replicate n x) := by simp only [replicate_succ]
    _ = length (replicate n x) + 1  := by simp only [length_cons]
    _ = n + 1                       := by simp only [succ_eq_add_one, HI]

-- 9ª demostración
-- ===============

lemma length_replicate_2 n (x : α) :
  length (replicate n x) = n :=
by induction n with
  | zero => calc
    length (replicate 0 x)
      = length ([] : List α)        := rfl
    _ = 0                           := rfl
  | succ n HI => calc
    length (replicate  (n + 1) x)
      = length (x :: replicate n x) := rfl
    _ = length (replicate n x) + 1  := rfl
    _ = n + 1                       := congrArg (. + 1) HI

-- 10ª demostración
-- ================

lemma length_replicate_3 n (x : α) :
  length (replicate n x) = n :=
by induction n with
  | zero      => simp
  | succ n HI => simp only [HI, replicate_succ, length_cons, Nat.succ_eq_add_one]

-- 11ª demostración
-- ===============

lemma length_replicate_4 :
  ∀ n, length (replicate n x) = n
| 0     => by simp
| (n+1) => by simp [*]

-- Lemas usados
-- ============

-- variable (xs : List α)
-- #check (length_cons x xs : length (x :: xs) = length xs + 1)
-- #check (length_nil : length [] = 0)
-- #check (length_replicate n x : length (replicate n x) = n)
-- #check (replicate_succ x n : replicate (n + 1) x = x :: replicate n x)
-- #check (replicate_zero x : replicate 0 x = [])
-- #check (succ_eq_add_one n : succ n = n + 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Pruebas_de_length_(replicaten x)_Ig_n.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Pruebas_de_length_(repeat_x_n)_Ig_n"
imports Main
begin

(* 1ª demostración⁾*)

lemma "length (replicate n x) = n"
proof (induct n)
  have "length (replicate 0 x) = length ([] :: 'a list)"
    by (simp only: replicate.simps(1))
  also have "… = 0"
    by (rule list.size(3))
  finally show "length (replicate 0 x) = 0"
    by this
next
  fix n
  assume HI : "length (replicate n x) = n"
  have "length (replicate (Suc n) x) =
        length (x # replicate n x)"
    by (simp only: replicate.simps(2))
  also have "… = length (replicate n x) + 1"
    by (simp only: list.size(4))
  also have "… = Suc n"
    by (simp only: HI)
  finally show "length (replicate (Suc n) x) = Suc n"
    by this
qed

(* 2ª demostración⁾*)

lemma "length (replicate n x) = n"
proof (induct n)
  show "length (replicate 0 x) = 0"
    by simp
next
  fix n
  assume "length (replicate n x) = n"
  then show "length (replicate (Suc n) x) = Suc n"
    by simp
qed

(* 3ª demostración⁾*)

lemma "length (replicate n x) = n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 4ª demostración⁾*)

lemma "length (replicate n x) = n"
  by (rule length_replicate)

end
</pre>
