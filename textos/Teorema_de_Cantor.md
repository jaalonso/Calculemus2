---
title: Teorema de Cantor
date: 2024-05-??? 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 el teorema de Cantor; es decir, que no existe ninguna aplicación suprayectiva de un conjunto en el conjunto de sus subconjuntos.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Function

variable {α : Type}

example : ∀ f : α → Set α, ¬Surjective f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \(f\) una función de \(A\) en el conjunto de los subconjuntos  \(A). Tenemos que demostrar que \(f\) no es suprayectiva. Lo haremos por reducción al absurdo. Para ello, supongamos que \(f\) es suprayectiva y consideremos el conjunto
\[ S := \{i ∈ A | i ∉ f(i)\} \tag{1} \]
Entonces, tiene que existir un \(j ∈ A\) tal que
\[ f(j) = S \tag{2} \]
Se pueden dar dos casos: \(j ∈ S\) ó \(j ∉ S\). Veamos que ambos son imposibles.

Caso 1: Supongamos que \(j ∈ S\). Entonces, por (1)
\[ j ∉ f(j) \]
y, por (2),
\[ j ∉ S \]
que es una contradicción.

Caso 2: Supongamos que \(j ∉ S\). Entonces, por (1)
\[ j ∈ f(j) \]
y, por (2),
\[ j ∈ S \]
que es una contradicción.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Function

variable {α : Type}

-- 1ª demostración
-- ===============

example : ∀ f : α → Set α, ¬Surjective f :=
by
  intros f hf
  -- f : α → Set α
  -- hf : Surjective f
  -- ⊢ False
  let S := {i | i ∉ f i}
  unfold Surjective at hf
  -- hf : ∀ (b : Set α), ∃ a, f a = b
  cases' hf S with j hj
  -- j : α
  -- hj : f j = S
  by_cases j ∈ S
  . -- h : j ∈ S
    dsimp at h
    -- h : ¬j ∈ f j
    apply h
    -- ⊢ j ∈ f j
    rw [hj]
    -- ⊢ j ∈ S
    exact h
  . -- h : ¬j ∈ S
    apply h
    -- ⊢ j ∈ S
    rw [←hj] at h
    -- h : ¬j ∈ f j
    exact h

-- 2ª demostración
-- ===============

example : ∀ f : α → Set α, ¬ Surjective f :=
by
  intros f hf
  -- f : α → Set α
  -- hf : Surjective f
  -- ⊢ False
  let S := {i | i ∉ f i}
  cases' hf S with j hj
  -- j : α
  -- hj : f j = S
  by_cases j ∈ S
  . -- h : j ∈ S
    apply h
    -- ⊢ j ∈ f j
    rwa [hj]
  . -- h : ¬j ∈ S
    apply h
    rwa [←hj] at h

-- 3ª demostración
-- ===============

example : ∀ f : α → Set α, ¬ Surjective f :=
by
  intros f hf
  -- f : α → Set α
  -- hf : Surjective f
  -- ⊢ False
  let S := {i | i ∉ f i}
  cases' hf S with j hj
  -- j : α
  -- hj : f j = S
  have h : (j ∈ S) = (j ∉ S) :=
    calc  (j ∈ S)
       = (j ∉ f j) := Set.mem_setOf_eq
     _ = (j ∉ S)   := congrArg (j ∉ .) hj
  exact iff_not_self (iff_of_eq h)

-- 4ª demostración
-- ===============

example : ∀ f : α → Set α, ¬ Surjective f :=
cantor_surjective

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (p : α → Prop)
-- variable (a b : Prop)
-- #check (Set.mem_setOf_eq : (x ∈ {y : α | p y}) = p x)
-- #check (iff_of_eq : a = b → (a ↔ b))
-- #check (iff_not_self : ¬(a ↔ ¬a))
-- #check (cantor_surjective : ∀ f : α → Set α, ¬ Surjective f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Teorema_de_Cantor.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
</pre>
