---
title: Teorema de Cantor
date: 2024-05-02 06:00:00 UTC+02:00
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

Sea \\(f\\) una función de \\(A\\) en el conjunto de los subconjuntos  \\(A\\). Tenemos que demostrar que \\(f\\) no es suprayectiva. Lo haremos por reducción al absurdo. Para ello, supongamos que \\(f\\) es suprayectiva y consideremos el conjunto
\\[ S := \\{i ∈ A | i ∉ f(i)\\} \\tag{1} \\]
Entonces, tiene que existir un \\(j ∈ A\\) tal que
\\[ f(j) = S \\tag{2} \\]
Se pueden dar dos casos: \\(j ∈ S\\) ó \\(j ∉ S\\). Veamos que ambos son imposibles.

Caso 1: Supongamos que \\(j ∈ S\\). Entonces, por (1)
\\[ j ∉ f(j) \\]
y, por (2),
\\[ j ∉ S \\]
que es una contradicción.

Caso 2: Supongamos que \\(j ∉ S\\). Entonces, por (1)
\\[ j ∈ f(j) \\]
y, por (2),
\\[ j ∈ S \\]
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
theory Teorema_de_Cantor
imports Main
begin

(* 1ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j"
    using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  show False
  proof (cases "j ∈ ?S")
    assume "j ∈ ?S"
    then have "j ∉ f j"
      by (rule CollectD)
    moreover
    have "j ∈ f j"
      using ‹?S = f j› ‹j ∈ ?S› by (rule subst)
    ultimately show False
      by (rule notE)
  next
    assume "j ∉ ?S"
    with ‹?S = f j› have "j ∉ f j"
      by (rule subst)
    then have "j ∈ ?S"
      by (rule CollectI)
    with ‹j ∉ ?S› show False
      by (rule notE)
  qed
qed

(* 2ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j"
    using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  have "j ∉ ?S"
  proof (rule notI)
    assume "j ∈ ?S"
    then have "j ∉ f j"
      by (rule CollectD)
    with ‹?S = f j› have "j ∉ ?S"
      by (rule ssubst)
    then show False
      using ‹j ∈ ?S› by (rule notE)
  qed
  moreover
  have "j ∈ ?S"
  proof (rule CollectI)
    show "j ∉ f j"
    proof (rule notI)
      assume "j ∈ f j"
      with ‹?S = f j› have "j ∈ ?S"
        by (rule ssubst)
      then have "j ∉ f j"
        by (rule CollectD)
      then show False
        using ‹j ∈ f j› by (rule notE)
    qed
  qed
  ultimately show False
    by (rule notE)
qed

(* 3ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j" using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j" by (rule exE)
  have "j ∉ ?S"
  proof
    assume "j ∈ ?S"
    then have "j ∉ f j" by simp
    with ‹?S = f j› have "j ∉ ?S" by simp
    then show False using ‹j ∈ ?S› by simp
  qed
  moreover
  have "j ∈ ?S"
  proof
    show "j ∉ f j"
    proof
      assume "j ∈ f j"
      with ‹?S = f j› have "j ∈ ?S" by simp
      then have "j ∉ f j" by simp
      then show False using ‹j ∈ f j› by simp
    qed
  qed
  ultimately show False by simp
qed

(* 4ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j"
    using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  have "j ∈ ?S = (j ∉ f j)"
    by (rule mem_Collect_eq)
  also have "… = (j ∉ ?S)"
    by (simp only: ‹?S = f j›)
  finally show False
    by (simp only: simp_thms(10))
qed

(* 5ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j" using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j" by (rule exE)
  have "j ∈ ?S = (j ∉ f j)" by simp
  also have "… = (j ∉ ?S)" using ‹?S = f j› by simp
  finally show False by simp
qed

(* 6ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
  unfolding surj_def
  by best

end
</pre>
