---
title: La equipotencia es una relación reflexiva
date: 2024-06-18 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Dos conjuntos \\(A\\) y \\(B\\) son equipotentes (y se denota por \\(A ≃ B\\)) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean por
<pre lang="lean">
   def es_equipotente (A B : Type _) : Prop :=
     ∃ g : A → B, Bijective g

   local infixr:50 " ⋍ " => es_equipotente
</pre>

Demostrar que la relación de equipotencia es reflexiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

open Function

def es_equipotente (A B : Type _) : Prop :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

example : Reflexive (. ⋍ .) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostra que para cualquier conjunto \\(X\\), se tiene que \\(X\\) es equipotente con \\(X\\). Para demostrarlo basta considerar que la función identidad en \\(X\\) es una biyección de \\(X\\) en \\(X\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

open Function

def es_equipotente (A B : Type _) : Prop :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

-- 1ª demostración
-- ===============

example : Reflexive (. ⋍ .) :=
by
  intro X
  -- ⊢ X ⋍ X
  use id
  -- ⊢ Bijective id
  exact bijective_id

-- 2ª demostración
-- ===============

example : Reflexive (. ⋍ .) :=
by
  intro X
  -- ⊢ X ⋍ X
  exact ⟨id, bijective_id⟩

-- 3ª demostración
-- ===============

example : Reflexive (. ⋍ .) :=
fun _ ↦ ⟨id, bijective_id⟩

-- Lemas usados
-- ============

-- #check (bijective_id : Bijective id)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_equipotencia_es_una_relacion_reflexiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_equipotencia_es_una_relacion_reflexiva
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)

lemma "reflp (≈)"
proof (rule reflpI)
  fix x :: "'a set"
  have "bij_betw id x x"
    by (simp only: bij_betw_id)
  then have "∃f. bij_betw f x x"
    by (simp only: exI)
  then show "x ≈ x"
    by (simp only: eqpoll_def)
qed

(* 2ª demostración *)

lemma "reflp (≈)"
by (simp only: reflpI eqpoll_refl)

(* 3ª demostración *)

lemma "reflp (≈)"
by (simp add: reflpI)

end
</pre>
