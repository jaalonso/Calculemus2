---
title: Pruebas de equivalencia de definiciones de inversa
date: 2024-08-19 06:00:00 UTC+02:00
category: Listas
has_math: true
---

[mathjax]

En Lean4, está definida la función

    reverse : List α → List α

tal que (reverse xs) es la lista obtenida invirtiendo el orden de los elementos de xs. Por ejemplo,

    reverse  [3,2,5,1] = [1,5,2,3]

Su definición es

    def reverseAux : List α → List α → List α
      | [],    ys => ys
      | x::xs, ys => reverseAux xs (x::ys)

    def reverse (xs : List α) : List α :=
      reverseAux xs []

Los siguientes lemas caracterizan su comportamiento

    reverseAux_nil : reverseAux [] ys = ys
    reverseAux_cons : reverseAux (x::xs) ys = reverseAux xs (x::ys)

Una definición alternativa es

    def reverse2 : List α → List α
      | []        => []
      | (x :: xs) => reverse2 xs ++ [x]

Demostrar que las dos definiciones son equivalentes; es decir,

    reverse xs = reverse2 xs

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (xs : List α)

example : reverse xs = reverse2 xs :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Es consecuencia del siguiente lema auxiliar

    (∀ xs, ys)[reverseAux xs ys = (reverse2 xs) ++ ys]

En efecto,

    reverse xs = reverseAux xs []
               = reverse2 xs ++ []    [por el lema auxiliar]
               = reverse2 xs

El lema auxiliar se demuestra por inducción en xs.

Caso base: Supongamos que xs = []. Entonces,

    reverseAux xs ys = reverseAux [] ys
                     = ys
                     = [] ++ ys
                     = reverse2 [] ++ ys
                     = reverse2 xs ++ ys

Paso de inducción: Supongamos que xs = a::as y la hipótesis de inducción (HI):

    (∀ ys)[reverseAux as ys = reverse2 as ++ ys]

Entonces,

    reverseAux xs ys = reverseAux (a :: as) ys
                     = reverseAux as (a :: ys)
                     = reverse2 as ++ (a :: ys)   [por HI]
                     = reverse2 as ++ ([a] ++ ys)
                     = (reverse2 as ++ [a]) ++ ys
                     = reverse2 (a :: as) ++ ys
                     = reverse2 xs ++ ys

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (x : α)
variable (xs ys : List α)

-- Reglas de simplifición de reverseAux
-- ====================================

@[simp]
lemma reverseAux_nil : reverseAux [] ys = ys := rfl

@[simp]
lemma reverseAux_cons : reverseAux (x::xs) ys = reverseAux xs (x::ys) := rfl

-- Definición y reglas de simplificación de reverse2
-- =================================================

def reverse2 : List α → List α
  | []        => []
  | (x :: xs) => reverse2 xs ++ [x]

@[simp]
lemma reverse2_nil :
  reverse2 ([] : List α) = [] :=
  rfl

@[simp]
lemma reverse2_cons :
  reverse2 (x :: xs) = reverse2 xs ++ [x] :=
  rfl

-- Lema auxiliar: reverseAux xs ys = (reverse2 xs) ++ ys
-- ======================================================

-- 1ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := reverseAux_nil ys
       _ = [] ++ ys                   := (nil_append ys).symm
       _ = reverse2 [] ++ ys          := congrArg (. ++ ys) reverse2_nil.symm
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := reverseAux_cons a as ys
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := congrArg (reverse2 as ++ .) singleton_append
       _ = (reverse2 as ++ [a]) ++ ys := (append_assoc (reverse2 as) [a] ys).symm
       _ = reverse2 (a :: as) ++ ys   := congrArg (. ++ ys) (reverse2_cons a as).symm

-- 2ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := by rw [reverseAux_nil]
       _ = [] ++ ys                   := by rw [nil_append]
       _ = reverse2 [] ++ ys          := by rw [reverse2_nil]
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by rw [reverseAux_cons]
       _ = reverse2 as ++ (a :: ys)   := by rw [(HI (a :: ys))]
       _ = reverse2 as ++ ([a] ++ ys) := by rw [singleton_append]
       _ = (reverse2 as ++ [a]) ++ ys := by rw [append_assoc]
       _ = reverse2 (a :: as) ++ ys   := by rw [reverse2_cons]

-- 3ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                := rfl
       _ = [] ++ ys          := by rfl
       _ = reverse2 [] ++ ys := rfl
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := rfl
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := rfl
       _ = (reverse2 as ++ [a]) ++ ys := by rw [append_assoc]
       _ = reverse2 (a :: as) ++ ys   := rfl

-- 3ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := by simp
       _ = [] ++ ys                   := by simp
       _ = reverse2 [] ++ ys          := by simp
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by simp
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := by simp
       _ = (reverse2 as ++ [a]) ++ ys := by simp
       _ = reverse2 (a :: as) ++ ys   := by simp

-- 4ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    simp
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by simp
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 (a :: as) ++ ys   := by simp

-- 5ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    simp
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    simp [HI (a :: ys)]

-- 6ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by induction' xs generalizing ys <;> simp [*]

-- 7ª demostración del lema auxiliar
example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    rw [reverseAux_nil]
    -- ⊢ ys = reverse2 [] ++ ys
    rw [reverse2_nil]
    -- ⊢ ys = [] ++ ys
    rw [nil_append]
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    rw [reverseAux_cons]
    -- ⊢ reverseAux as (a :: ys) = reverse2 (a :: as) ++ ys
    rw [(HI (a :: ys))]
    -- ⊢ reverse2 as ++ a :: ys = reverse2 (a :: as) ++ ys
    rw [reverse2_cons]
    -- ⊢ reverse2 as ++ a :: ys = (reverse2 as ++ [a]) ++ ys
    rw [append_assoc]
    -- ⊢ reverse2 as ++ a :: ys = reverse2 as ++ ([a] ++ ys)
    rw [singleton_append]

-- 8ª demostración  del lema auxiliar
-- ==================================

@[simp]
lemma reverse2_equiv :
  ∀ xs : List α, ∀ ys, reverseAux xs ys = (reverse2 xs) ++ ys
| []         => by simp
| (a :: as)  => by simp [reverse2_equiv as]

-- Demostraciones del lema principal
-- =================================

-- 1ª demostración
-- ===============

example : reverse xs = reverse2 xs :=
calc reverse xs
     = reverseAux xs []  := rfl
   _ = reverse2 xs ++ [] := by rw [reverse2_equiv]
   _ = reverse2 xs       := by rw [append_nil]

-- 2ª demostración
-- ===============

example : reverse xs = reverse2 xs :=
by simp [reverse2_equiv, reverse]

-- 3ª demostración
-- ===============

example : reverse xs = reverse2 xs :=
by simp [reverse]

-- Lemas usados
-- ============

-- variable (ys zs : List α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (append_nil xs : xs ++ [] = xs)
-- #check (nil_append xs : [] ++ xs = xs)
-- #check (reverse xs = reverseAux xs [])
-- #check (singleton_append : [x] ++ ys = x :: ys)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Pruebas_de_equivalencia_de_definiciones_de_inversa.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Pruebas_de_equivalencia_de_definiciones_de_inversa
imports Main
begin

(* Definición alternativa *)
(* ====================== *)

fun inversa_aux :: "'a list ⇒ 'a list ⇒ 'a list" where
  "inversa_aux [] ys     = ys"
| "inversa_aux (x#xs) ys = inversa_aux xs (x#ys)"

fun inversa :: "'a list ⇒ 'a list" where
  "inversa xs = inversa_aux xs []"

(* Lema auxiliar: inversa_aux xs ys = (rev xs) @ ys *)
(* ================================================ *)

(* 1ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "inversa_aux [] ys = ys"
    by (simp only: inversa_aux.simps(1))
  also have "… = [] @ ys"
    by (simp only: append.simps(1))
  also have "… = rev [] @ ys"
    by (simp only: rev.simps(1))
  finally show "inversa_aux [] ys = rev [] @ ys"
    by this
next
  fix a ::'a and xs :: "'a list"
  assume HI: "⋀ys. inversa_aux xs ys = rev xs@ys"
  show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = inversa_aux xs (a#ys)"
      by (simp only: inversa_aux.simps(2))
    also have "… = rev xs@(a#ys)"
      by (simp only: HI)
    also have "… = rev xs @ ([a] @ ys)"
      by (simp only: append.simps)
    also have "… = (rev xs @ [a]) @ ys"
      by (simp only: append_assoc)
    also have "… = rev (a # xs) @ ys"
      by (simp only: rev.simps(2))
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys"
      by this
  qed
qed

(* 2ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "inversa_aux [] ys = ys" by simp
  also have "… = [] @ ys" by simp
  also have "… = rev [] @ ys" by simp
  finally show "inversa_aux [] ys = rev [] @ ys" .
next
  fix a ::'a and xs :: "'a list"
  assume HI: "⋀ys. inversa_aux xs ys = rev xs@ys"
  show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = inversa_aux xs (a#ys)" by simp
    also have "… = rev xs@(a#ys)" using HI by simp
    also have "… = rev xs @ ([a] @ ys)" by simp
    also have "… = (rev xs @ [a]) @ ys" by simp
    also have "… = rev (a # xs) @ ys" by simp
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* 3ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  show "inversa_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume HI: "⋀ys. inversa_aux xs ys = rev xs@ys"
  show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = rev xs@(a#ys)" using HI by simp
    also have "… = rev (a # xs) @ ys" by simp
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* 4ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  show "⋀ys. inversa_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume "⋀ys. inversa_aux xs ys = rev xs@ys"
  then show "⋀ys. inversa_aux (a#xs) ys = rev (a#xs)@ys" by simp
qed

(* 5ª demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 6ª demostración del lema auxiliar *)
lemma inversa_equiv:
  "inversa_aux xs ys = (rev xs) @ ys"
by (induct xs arbitrary: ys) simp_all

(* Demostraciones del lema principal *)
(* ================================= *)

(* 1ª demostración *)
lemma "inversa xs = rev xs"
proof -
  have "inversa xs = inversa_aux xs []"
    by (rule inversa.simps)
  also have "… = (rev xs) @ []"
    by (rule inversa_equiv)
  also have "… = rev xs"
    by (rule append.right_neutral)
  finally show "inversa xs = rev xs"
    by this
qed

(* 2ª demostración *)
lemma "inversa xs = rev xs"
proof -
  have "inversa xs = inversa_aux xs []"  by simp
  also have "… = (rev xs) @ []" by (rule inversa_equiv)
  also have "… = rev xs" by simp
  finally show "inversa xs = rev xs" .
qed

(* 3ª demostración *)
lemma "inversa xs = rev xs"
by (simp add: inversa_equiv)

end
</pre>
