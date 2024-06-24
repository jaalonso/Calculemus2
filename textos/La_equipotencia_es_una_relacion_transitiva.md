---
title: La equipotencia es una relación transitiva
date: 2024-06-24 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Dos conjuntos \\(A\\) y \\(B\\) son equipotentes (y se denota por \\(A ≃ B\\)) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean4 por
<pre lang="lean">
   def es_equipotente (A B : Type _) : Prop :=
     ∃ g : A → B, Bijective g

   local infixr:50 " ⋍ " => es_equipotente
</pre>

Demostrar con Lean4 que la relación de equipotencia es transitiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

def es_equipotente (A B : Type _) :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

example : Transitive (. ⋍ .) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(X\\), \\(Y\\), \\(Z\\) tales que \\(X ⋍ Y\\) y \\(Y ⋍ Z\\). Entonces, existen \\(f: X → Y\\) y \\(g: Y → Z\\) que son biyectivas. Por tanto, \\(g ∘ f: X → Z\\) es biyectiva y \\(X ⋍ Z\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

def es_equipotente (A B : Type _) :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

-- 1ª demostración
-- ===============

example : Transitive (. ⋍ .) :=
by
  intro X Y Z hXY hYZ
  -- X Y Z : Type ?u.8772
  -- hXY : X ⋍ Y
  -- hYZ : Y ⋍ Z
  -- ⊢ X ⋍ Z
  unfold es_equipotente at *
  -- hXY : ∃ g, Bijective g
  -- hYZ : ∃ g, Bijective g
  -- ⊢ ∃ g, Bijective g
  cases' hXY with f hf
  -- f : X → Y
  -- hf : Bijective f
  cases' hYZ with g hg
  -- g : Y → Z
  -- hg : Bijective g
  use (g ∘ f)
  -- ⊢ Bijective (g ∘ f)
  exact Bijective.comp hg hf

-- 2ª demostración
-- ===============

example : Transitive (. ⋍ .) :=
by
  rintro X Y Z ⟨f, hf⟩ ⟨g, hg⟩
  -- X Y Z : Type ?u.8990
  -- f : X → Y
  -- hf : Bijective f
  -- g : Y → Z
  -- hg : Bijective g
  -- ⊢ X ⋍ Z
  exact ⟨g ∘ f, Bijective.comp hg hf⟩

-- 3ª demostración
-- ===============

example : Transitive (. ⋍ .) :=
fun _ _ _ ⟨f, hf⟩ ⟨g, hg⟩ ↦ ⟨g ∘ f, Bijective.comp hg hf⟩

-- Lemas usados
-- ============

-- variable {X Y Z : Type}
-- variable {f : X → Y}
-- variable {g : Y → Z}
-- #check (Bijective.comp : Bijective g → Bijective f → Bijective (g ∘ f))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_equipotencia_es_una_relacion_transitiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_equipotencia_es_una_relacion_transitiva
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)

lemma "transp (≈)"
proof (rule transpI)
  fix x y z :: "'a set"
  assume "x ≈ y" and "y ≈ z"
  show "x ≈ z"
  proof (unfold eqpoll_def)
    obtain f where hf : "bij_betw f x y"
      using ‹x ≈ y› eqpoll_def by auto
    obtain g where hg : "bij_betw g y z"
      using ‹y ≈ z› eqpoll_def by auto
    have "bij_betw (g ∘ f) x z"
      using hf hg by (rule bij_betw_trans)
    then show "∃h. bij_betw h x z"
      by auto
  qed
qed

(* 2ª demostración *)

lemma "transp (≈)"
  unfolding eqpoll_def transp_def
  by (meson bij_betw_trans)

(* 3ª demostración *)

lemma "transp (≈)"
  by (simp add: eqpoll_trans transpI)

end
</pre>
