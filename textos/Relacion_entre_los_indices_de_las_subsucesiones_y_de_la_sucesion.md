---
title: Relación entre los índices de las subsucesiones y de la sucesión
date: 2024-07-10 06:00:00 UTC+02:00
category: Sucesiones
has_math: true
---

[mathjax]

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
\\[ uₒ, u₂, u₄, u₆, ... \\]
se ha obtenido con la función de extracción \\(ϕ\\) tal que \\(ϕ(n) = 2n\\).

En Lean4, se puede definir que \\(ϕ\\) es una función de extracción por
<pre lang="lean">
   def extraccion (ϕ : ℕ → ℕ) :=
     ∀ {n m}, n < m → ϕ n < ϕ m
</pre>

Demostrarcon Lean4 que si \\(ϕ\\) es una función de extracción, entonces
\\[ (∀ n)[n ≤ ϕ(n) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Nat

variable {ϕ : ℕ → ℕ}

def extraccion (ϕ : ℕ → ℕ) :=
  ∀ {n m}, n < m → ϕ n < ϕ m

example :
  extraccion ϕ → ∀ n, n ≤ ϕ n :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se demuestra por inducción en \\(n\\).

**Base de la inducción**: Como \\(0\\) es el menor número natural, se tiene que
\\[ 0 ≤ ϕ(0) \\]

**Paso de inducción**: Sea \\(m ∈ ℕ\\) y supongamos que la hipótesis de inducción
\\[ m ≤ ϕ(m) \\tag{text{HI}) \\]

Puesto que \\(ϕ\\) es una función de extracción,
\\[ ϕ(m) < ϕ(m+1) \\tag{1} \\]
De (HI) y (1) se tiene que
\\[ m < ϕ(m+1) \\]
Por tanto,
\\[ m+1 ≤ ϕ(m+1) \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Nat

variable {ϕ : ℕ → ℕ}

def extraccion (ϕ : ℕ → ℕ) :=
  ∀ {n m}, n < m → ϕ n < ϕ m

-- 1ª demostración
-- ===============

example :
  extraccion ϕ → ∀ n, n ≤ ϕ n :=
by
  intros h n
  -- h : extraccion ϕ
  -- n : ℕ
  -- ⊢ n ≤ ϕ n
  induction' n with m HI
  . -- ⊢ zero ≤ ϕ zero
    exact Nat.zero_le (ϕ 0)
  . -- m : ℕ
    -- HI : m ≤ ϕ m
    -- ⊢ succ m ≤ ϕ (succ m)
    apply Nat.succ_le_of_lt
    -- ⊢ m < ϕ (succ m)
    have h1 : m < succ m := lt_add_one m
    calc m ≤ ϕ m        := HI
         _ < ϕ (succ m) := h h1

-- 2ª demostración
-- ===============

example :
  extraccion ϕ → ∀ n, n ≤ ϕ n :=
by
  intros h n
  -- h : extraccion ϕ
  -- n : ℕ
  -- ⊢ n ≤ ϕ n
  induction' n with m HI
  . -- ⊢ zero ≤ ϕ zero
    exact Nat.zero_le (ϕ 0)
  . -- ⊢ succ m ≤ ϕ (succ m)
    have h1 : m < ϕ (succ m) :=
      calc m ≤ ϕ m        := HI
           _ < ϕ (succ m) := h (lt_add_one m)
    exact Nat.succ_le_of_lt h1

-- Lemas usados
-- ============

-- variable (m n : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (lt_add_one n : n < n + 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion
imports Main
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

(* En la demostración se usará el siguiente lema *)

lemma extraccionE:
  assumes "extraccion φ"
          "n < m"
  shows   "φ n < φ m"
proof -
  have "∀ n m. n < m ⟶ φ n < φ m"
    using assms(1) by (unfold extraccion_def)
  then have "n < m ⟶ φ n < φ m"
    by (elim allE)
  then show "φ n < φ m"
    using assms(2) by (rule mp)
qed

(* 1ª demostración *)

lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by (rule le0)
next
  fix n
  assume "n ≤ φ n"
  also have "φ n < φ (Suc n)"
  proof -
    have "n < Suc n"
      by (rule lessI)
    with assms show "φ n < φ (Suc n)"
      by (rule extraccionE)
  qed
  finally show "Suc n ≤ φ (Suc n)"
    by (rule Suc_leI)
qed

(* 2ª demostración *)

lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by (rule le0)
next
  fix n
  assume "n ≤ φ n"
  also have "… < φ (Suc n)"
  using assms
  proof (rule extraccionE)
    show "n < Suc n"
      by (rule lessI)
  qed
  finally show "Suc n ≤ φ (Suc n)"
    by (rule Suc_leI)
qed

(* 3ª demostración *)

lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by (rule le0)
next
  fix n
  assume "n ≤ φ n"
  also have "… < φ (Suc n)"
    by (rule extraccionE [OF assms lessI])
  finally show "Suc n ≤ φ (Suc n)"
    by (rule Suc_leI)
qed

(* 4ª demostración *)

lemma
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0"
    by simp
next
  fix n
  assume HI : "n ≤ φ n"
  also have "φ n < φ (Suc n)"
    using assms extraccion_def by blast
  finally show "Suc n ≤ φ (Suc n)"
    by simp
qed

end
</pre>
