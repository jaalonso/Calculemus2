---
title: Las funciones de extracción no están acotadas
date: 2024-07-11 06:00:00 UTC+02:00
category: Sucesiones
has_math: true
---

[mathjax]

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
\\[ u_0, u_2, u_4, u_6, ... \\]
se ha obtenido con la función de extracción \\(ϕ\\) tal que \\(ϕ(n) = 2n\\).

En Lean4, se puede definir que \\(ϕ\\) es una función de extracción por
<pre lang="lean">
   def extraccion (ϕ : ℕ → ℕ) :=
     ∀ n m, n < m → ϕ n < ϕ m
</pre>

Demostrar que las funciones de extracción no están acotadas; es decir, que si \\(ϕ\\) es una función de extracción, entonces
\\[ (∀ N, N')(∃ n ≥ N')[ϕ(n) ≥ N \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Nat

variable {ϕ : ℕ → ℕ}

def extraccion (ϕ : ℕ → ℕ) :=
  ∀ n m, n < m → ϕ n < ϕ m

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En la demostración se usará como lema auxiliar el resultado del ejercicio anterior; es decir, que si \\(ϕ\\) es una función de extracción, entonces
\\[ (∀ n)[n ≤ ϕ(n)] \\]

Sea \\(ϕ\\) una función de extracción y \\(N, N' ∈ ℕ\\). Definimos
\\[ n = máx(N, N') \\]
Entonces de tiene que
\\[ n ≥ N' \\]
y, además,
\\begin{align}
   N &≤ n       \\\\
     &≤ ϕ(n)    &&\\text{[por el Lema]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Nat

variable {ϕ : ℕ → ℕ}

def extraccion (ϕ : ℕ → ℕ) :=
  ∀ n m, n < m → ϕ n < ϕ m

-- En la demostración se usará el siguiente lema auxiliar, demostrado en
-- el ejercicio anterior

lemma aux
  (h : extraccion ϕ)
  : ∀ n, n ≤ ϕ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (ϕ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ ϕ m        := HI
         _ < ϕ (succ m) := h m (m+1) (lt_add_one m)

-- 1ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  let n := max N N'
  use n
  -- ⊢ n ≥ N' ∧ ϕ n ≥ N
  constructor
  . -- ⊢ n ≥ N'
    exact le_max_right N N'
  . -- ⊢ ϕ n ≥ N
    calc N ≤ n   := le_max_left N N'
         _ ≤ ϕ n := aux h n

-- 2ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  let n := max N N'
  use n
  -- ⊢ n ≥ N' ∧ ϕ n ≥ N
  constructor
  . -- ⊢ n ≥ N'
    exact le_max_right N N'
  . -- ⊢ ϕ n ≥ N
    exact le_trans (le_max_left N N')
                   (aux h n)

-- 3ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  use max N N'
  -- ⊢ max N N' ≥ N' ∧ ϕ (max N N') ≥ N
  constructor
  . -- ⊢ max N N' ≥ N'
    exact le_max_right N N'
  . -- ⊢ ϕ (max N N') ≥ N
    exact le_trans (le_max_left N N')
                   (aux h (max N N'))

-- 4ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
by
  intros N N'
  -- N N' : ℕ
  -- ⊢ ∃ n, n ≥ N' ∧ ϕ n ≥ N
  use max N N'
  -- ⊢ max N N' ≥ N' ∧ ϕ (max N N') ≥ N
  exact ⟨le_max_right N N',
         le_trans (le_max_left N N')
                  (aux h (max N N'))⟩

-- 5ª demostración
-- ===============

example
  (h : extraccion ϕ)
  : ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
fun N N' ↦ ⟨max N N', ⟨le_max_right N N',
                       le_trans (le_max_left N N')
                                (aux h (max N N'))⟩⟩

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_funciones_de_extraccion_no_estan_acotadas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_funciones_de_extraccion_no_estan_acotadas
imports Main
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

(* En la demostración se usará el siguiente lema *)

lemma aux :
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

(* 1ª demostración *)

lemma
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  let ?k = "max N N'"
  have "max N N' ≤ ?k"
    by (rule le_refl)
  then have hk : "N ≤ ?k ∧ N' ≤ ?k"
    by (simp only: max.bounded_iff)
  then have "?k ≥ N'"
    by (rule conjunct2)
  moreover
  have "N ≤ φ ?k"
  proof -
    have "N ≤ ?k"
      using hk by (rule conjunct1)
    also have "… ≤ φ ?k"
      using assms by (rule aux)
    finally show "N ≤ φ ?k"
      by this
  qed
  ultimately have "?k ≥ N' ∧ φ ?k ≥ N"
    by (rule conjI)
  then show "∃k ≥ N'. φ k ≥ N"
    by (rule exI)
qed

(* 2ª demostración *)

lemma
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  let ?k = "max N N'"
  have "?k ≥ N'"
    by simp
  moreover
  have "N ≤ φ ?k"
  proof -
    have "N ≤ ?k"
      by simp
    also have "… ≤ φ ?k"
      using assms by (rule aux)
    finally show "N ≤ φ ?k"
      by this
  qed
  ultimately show "∃k ≥ N'. φ k ≥ N"
    by blast
qed

end
</pre>
