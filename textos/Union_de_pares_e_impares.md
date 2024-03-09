---
Título: Pares ∪ Impares = Naturales.
Autor:  José A. Alonso
---

[mathjax]

Los conjuntos de los números naturales, de los pares y de los impares se definen en Lean4 por
<pre lang="haskell">
   def Naturales : Set ℕ := {n | True}
   def Pares     : Set ℕ := {n | Even n}
   def Impares   : Set ℕ := {n | ¬Even n}
</pre>

Demostrar con Lean4 que
<pre lang="haskell">
   Pares ∪ Impares = Naturales
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.Parity
open Set

def Naturales : Set ℕ := {n | True}
def Pares     : Set ℕ := {n | Even n}
def Impares   : Set ℕ := {n | ¬Even n}

example : Pares ∪ Impares = Naturales :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que
\\[ \\{n | \\text{Even}(n)\\} ∪ \\{n | ¬\\text{Even}(n)\\} = \\{n | \\text{True}\\} \\]
es decir,
\\[ n ∈ \\{n | \\text{Even}(n)\\} ∪ \\{n | ¬\\text{Even}(n)\\} ↔ n ∈ \\{n | \\text{True}\\} \\]
que se reduce a
\\[ ⊢ \\text{Even}(n) ∨ ¬\\text{Even}(n) \\]
que es una tautología.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Nat.Parity
open Set

def Naturales : Set ℕ := {n | True}
def Pares     : Set ℕ := {n | Even n}
def Impares   : Set ℕ := {n | ¬Even n}

-- 1ª demostración
-- ===============

example : Pares ∪ Impares = Naturales :=
by
  unfold Pares Impares Naturales
  -- ⊢ {n | Even n} ∪ {n | ¬Even n} = {n | True}
  ext n
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
  simp
  -- ⊢ Even n ∨ ¬Even n
  exact em (Even n)

-- 2ª demostración
-- ===============

example : Pares ∪ Impares = Naturales :=
by
  unfold Pares Impares Naturales
  -- ⊢ {n | Even n} ∪ {n | ¬Even n} = {n | True}
  ext n
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
  tauto
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Union_de_pares_e_impares.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Union_de_pares_e_impares
imports Main
begin

definition naturales :: "nat set" where
  "naturales = {n∈ℕ . True}"

definition pares :: "nat set" where
  "pares = {n∈ℕ . even n}"

definition impares :: "nat set" where
  "impares = {n∈ℕ . ¬ even n}"

(* 1ª demostración *)
lemma "pares ∪ impares = naturales"
proof -
  have "∀ n ∈ ℕ . even n ∨ ¬ even n ⟷ True"
    by simp
  then have "{n ∈ ℕ. even n} ∪ {n ∈ ℕ. ¬ even n} = {n ∈ ℕ. True}"
    by auto
  then show "pares ∪ impares = naturales"
    by (simp add: naturales_def pares_def impares_def)
qed

(* 2ª demostración *)
lemma "pares ∪ impares = naturales"
  unfolding naturales_def pares_def impares_def
  by auto

end
</pre>
