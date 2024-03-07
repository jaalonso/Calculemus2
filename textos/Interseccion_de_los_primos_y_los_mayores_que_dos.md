---
Título: Los primos mayores que 2 son impares.
Autor:  José A. Alonso
---

[mathjax]

Los números primos, los mayores que 2 y los impares se definen en Lean4 por
<pre lang="lean">
   def Primos      : Set ℕ := {n | Nat.Prime n}
   def MayoresQue2 : Set ℕ := {n | n > 2}
   def Impares     : Set ℕ := {n | ¬Even n}
</pre>

Demostrar con Lean4 que
<pre lang="lean">
   Primos ∩ MayoresQue2 ⊆ Impares
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

def Primos      : Set ℕ := {n | Nat.Prime n}
def MayoresQue2 : Set ℕ := {n | n > 2}
def Impares     : Set ℕ := {n | ¬Even n}

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by sorry
</pre>
<!--more-->

<h2>1. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

def Primos      : Set ℕ := {n | Nat.Prime n}
def MayoresQue2 : Set ℕ := {n | n > 2}
def Impares     : Set ℕ := {n | ¬Even n}

-- 1ª demostración
-- ===============

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by
  unfold Primos MayoresQue2 Impares
  -- ⊢ {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬Even n}
  intro n
  -- n : ℕ
  -- ⊢ n ∈ {n | Nat.Prime n} ∩ {n | n > 2} → n ∈ {n | ¬Even n}
  simp
  -- ⊢ Nat.Prime n → 2 < n → ¬Even n
  intro hn
  -- hn : Nat.Prime n
  -- ⊢ 2 < n → ¬Even n
  rcases Prime.eq_two_or_odd hn with (h | h)
  . -- h : n = 2
    rw [h]
    -- ⊢ 2 < 2 → ¬Even 2
    intro h1
    -- h1 : 2 < 2
    -- ⊢ ¬Even 2
    exfalso
    exact absurd h1 (lt_irrefl 2)
  . -- h : n % 2 = 1
    rw [even_iff]
    -- ⊢ 2 < n → ¬n % 2 = 0
    rw [h]
    -- ⊢ 2 < n → ¬1 = 0
    intro
    -- a : 2 < n
    -- ⊢ ¬1 = 0
    exact one_ne_zero

-- 2ª demostración
-- ===============

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by
  unfold Primos MayoresQue2 Impares
  -- ⊢ {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬Even n}
  rintro n ⟨h1, h2⟩
  -- n : ℕ
  -- h1 : n ∈ {n | Nat.Prime n}
  -- h2 : n ∈ {n | n > 2}
  -- ⊢ n ∈ {n | ¬Even n}
  simp at *
  -- h1 : Nat.Prime n
  -- h2 : 2 < n
  -- ⊢ ¬Even n
  rcases Prime.eq_two_or_odd h1 with (h3 | h4)
  . -- h3 : n = 2
    rw [h3] at h2
    -- h2 : 2 < 2
    exfalso
    -- ⊢ False
    exact absurd h2 (lt_irrefl 2)
  . -- h4 : n % 2 = 1
    rw [even_iff]
    -- ⊢ ¬n % 2 = 0
    rw [h4]
    -- ⊢ ¬1 = 0
    exact one_ne_zero

-- 3ª demostración
-- ===============

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by
  unfold Primos MayoresQue2 Impares
  -- ⊢ {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬Even n}
  rintro n ⟨h1, h2⟩
  -- n : ℕ
  -- h1 : n ∈ {n | Nat.Prime n}
  -- h2 : n ∈ {n | n > 2}
  -- ⊢ n ∈ {n | ¬Even n}
  simp at *
  -- h1 : Nat.Prime n
  -- h2 : 2 < n
  -- ⊢ ¬Even n
  rcases Prime.eq_two_or_odd h1 with (h3 | h4)
  . -- h3 : n = 2
    rw [h3] at h2
    -- h2 : 2 < 2
    linarith
  . -- h4 : n % 2 = 1
    rw [even_iff]
    -- ⊢ ¬n % 2 = 0
    linarith

-- Lemas usados
-- ============

-- variable (p n : ℕ)
-- variable (a b : Prop)
-- #check (Prime.eq_two_or_odd : Nat.Prime p → p = 2 ∨ p % 2 = 1)
-- #check (absurd : a → ¬a → b)
-- #check (even_iff : Even n ↔ n % 2 = 0)
-- #check (lt_irrefl n : ¬n < n)
-- #check (one_ne_zero : 1 ≠ 0)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Interseccion_de_los_primos_y_los_mayores_que_dos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Interseccion_de_los_primos_y_los_mayores_que_dos
imports Main "HOL-Number_Theory.Number_Theory"
begin

definition primos :: "nat set" where
  "primos = {n ∈ ℕ . prime n}"

definition mayoresQue2 :: "nat set" where
  "mayoresQue2 = {n ∈ ℕ . n > 2}"

definition impares :: "nat set" where
  "impares = {n ∈ ℕ . ¬ even n}"

(* 1ª demostración *)
lemma "primos ∩ mayoresQue2 ⊆ impares"
proof
  fix x
  assume "x ∈ primos ∩ mayoresQue2"
  then have "x ∈ ℕ ∧ prime x ∧ 2 < x"
    by (simp add: primos_def mayoresQue2_def)
  then have "x ∈ ℕ ∧ odd x"
    by (simp add: prime_odd_nat)
  then show "x ∈ impares"
    by (simp add: impares_def)
qed

(* 2ª demostración *)
lemma "primos ∩ mayoresQue2 ⊆ impares"
  unfolding primos_def mayoresQue2_def impares_def
  by (simp add: Collect_mono_iff Int_def prime_odd_nat)

(* 3ª demostración *)
lemma "primos ∩ mayoresQue2 ⊆ impares"
  unfolding primos_def mayoresQue2_def impares_def
  by (auto simp add: prime_odd_nat)

end
</pre>
