---
title: Asociatividad de la concatenación de listas
date: 2024-07-31 06:00:00 UTC+02:00
category: Listas
has_math: true
---

[mathjax]

En Lean4 la operación de concatenación de listas se representa por (++) y está caracterizada por los siguientes lemas

    nil_append  : [] ++ ys = ys
    cons_append : (x :: xs) ++ y = x :: (xs ++ ys)

Demostrar que la concatenación es asociativa; es decir,

    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs


Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (xs ys zs : List α)

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por inducción en xs.

Caso base: Supongamos que xs = [], entonces

    xs ++ (ys ++ zs) = [] ++ (ys ++ zs)
                     = ys ++ zs
                     = ([] ++ ys) ++ zs
                     = (xs ++ ys) ++ zs

Paso de inducción: Supongamos que xs = a :: as y la hipótesis de inducción

    as ++ (ys ++ zs) = (as ++ ys) + zs                            (HI)

Entonces

    xs ++ (ys ++ zs) = (a :: as) ++ (ys ++ zs)
                     = a :: (as ++ (ys ++ zs))
                     = a :: ((as ++ ys) ++ zs)    [por HI]
                     = (a :: (as ++ ys)) ++ zs
                     = ((a :: as) ++ ys) ++ zs
                     = (xs ++ ys) ++ zs

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (xs ys zs : List α)

-- 1ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := nil_append (ys ++ zs)
       _ = ([] ++ ys) ++ zs        := congrArg (. ++ zs) (nil_append ys).symm
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := cons_append a as (ys ++ zs)
       _ = a :: ((as ++ ys) ++ zs) := congrArg (a :: .) HI
       _ = (a :: (as ++ ys)) ++ zs := (cons_append a (as ++ ys) zs).symm

-- 2ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := by rw [nil_append]
       _ = ([] ++ ys) ++ zs        := by rw [nil_append]
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := by rw [cons_append]
       _ = a :: ((as ++ ys) ++ zs) := by rw [HI]
       _ = (a :: (as ++ ys)) ++ zs := by rw [cons_append]
       _ = ((a :: as) ++ ys) ++ zs := by rw [← cons_append]

-- 3ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := by exact rfl
       _ = ([] ++ ys) ++ zs        := by exact rfl
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := rfl
       _ = a :: ((as ++ ys) ++ zs) := by rw [HI]
       _ = (a :: (as ++ ys)) ++ zs := rfl
       _ = ((a :: as) ++ ys) ++ zs := rfl

-- 4ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . calc [] ++ (ys ++ zs)
         = ys ++ zs                := by simp
       _ = ([] ++ ys) ++ zs        := by simp
  . calc (a :: as) ++ (ys ++ zs)
         = a :: (as ++ (ys ++ zs)) := by simp
       _ = a :: ((as ++ ys) ++ zs) := congrArg (a :: .) HI
       _ = (a :: (as ++ ys)) ++ zs := by simp
       _ = ((a :: as) ++ ys) ++ zs := by simp

-- 5ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . simp
  . exact (cons_inj a).mpr HI

-- 6ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction' xs with a as HI
  . -- ⊢ [] ++ (ys ++ zs) = ([] ++ ys) ++ zs
    rw [nil_append]
    -- ⊢ ys ++ zs = ([] ++ ys) ++ zs
    rw [nil_append]
  . -- a : α
    -- as : List α
    -- HI : as ++ (ys ++ zs) = as ++ ys ++ zs
    -- ⊢ (a :: as) ++ (ys ++ zs) = ((a :: as) ++ ys) ++ zs
    rw [cons_append]
    -- ⊢ a :: (as ++ (ys ++ zs)) = ((a :: as) ++ ys) ++ zs
    rw [HI]
    -- ⊢ a :: ((as ++ ys) ++ zs) = ((a :: as) ++ ys) ++ zs
    rw [cons_append]
    -- ⊢ a :: ((as ++ ys) ++ zs) = (a :: (as ++ ys)) ++ zs
    rw [cons_append]

-- 7ª demostración
-- ===============

lemma conc_asoc_1 (xs ys zs : List α) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by
  induction xs with
  | nil => calc
    [] ++ (ys ++ zs)
        = ys ++ zs         := by rw [nil_append]
      _ = ([] ++ ys) ++ zs := by rw [nil_append]
  | cons a as HI => calc
    (a :: as) ++ (ys ++ zs)
        = a :: (as ++ (ys ++ zs)) := by rw [cons_append]
      _ = a :: ((as ++ ys) ++ zs) := by rw [HI]
      _ = (a :: (as ++ ys)) ++ zs := by rw [cons_append]
      _ = ((a :: as) ++ ys) ++ zs := congrArg (. ++ zs) (cons_append a as ys)


-- 8ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs  :=
(append_assoc xs ys zs).symm

-- 9ª demostración
-- ===============

example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
by simp

-- Lemas usados
-- ============

-- variable (x : α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (cons_append x xs ys : (x :: xs) ++ ys = x :: (xs ++ ys))
-- #check (cons_inj x : x :: xs = x :: ys ↔ xs = ys)
-- #check (nil_append xs : [] ++ xs = xs)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Asociatividad_de_la_concatenacion_de_listas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Asociatividad_de_la_concatenacion_de_listas
imports Main
begin

(* 1ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  have "[] @ (ys @ zs) = ys @ zs"
    by (simp only: append_Nil)
  also have "… = ([] @ ys) @ zs"
    by (simp only: append_Nil)
  finally show "[] @ (ys @ zs) = ([] @ ys) @ zs"
    by this
next
  fix x xs
  assume HI : "xs @ (ys @ zs) = (xs @ ys) @ zs"
  have "(x # xs) @ (ys @ zs) = x # (xs @ (ys @ zs))"
    by (simp only: append_Cons)
  also have "… = x # ((xs @ ys) @ zs)"
    by (simp only: HI)
  also have "… = (x # (xs @ ys)) @ zs"
    by (simp only: append_Cons)
  also have "… = ((x # xs) @ ys) @ zs"
    by (simp only: append_Cons)
  finally show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs"
    by this
qed

(* 2ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  have "[] @ (ys @ zs) = ys @ zs" by simp
  also have "… = ([] @ ys) @ zs" by simp
  finally show "[] @ (ys @ zs) = ([] @ ys) @ zs" .
next
  fix x xs
  assume HI : "xs @ (ys @ zs) = (xs @ ys) @ zs"
  have "(x # xs) @ (ys @ zs) = x # (xs @ (ys @ zs))" by simp
  also have "… = x # ((xs @ ys) @ zs)" by simp
  also have "… = (x # (xs @ ys)) @ zs" by simp
  also have "… = ((x # xs) @ ys) @ zs" by simp
  finally show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs" .
qed

(* 3ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  show "[] @ (ys @ zs) = ([] @ ys) @ zs" by simp
next
  fix x xs
  assume "xs @ (ys @ zs) = (xs @ ys) @ zs"
  then show "(x # xs) @ (ys @ zs) = ((x # xs) @ ys) @ zs" by simp
qed

(* 4ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 5ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by (rule append_assoc [symmetric])

(* 6ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by (induct xs) simp_all

(* 7ª demostración *)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by simp

end
</pre>
