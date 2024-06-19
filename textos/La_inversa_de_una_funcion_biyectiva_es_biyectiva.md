---
title: La inversa de una función es biyectiva
date: 2024-06-19 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

En Lean4 se puede definir que \\(g\\) es una inversa de \\(f\\) por
<pre lang="lean">
   def inversa (f : X → Y) (g : Y → X) :=
     (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
</pre>

Demostrar que si \\(g\\) es una inversa de \\(f\\), entonces \\(g\\) es biyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y : Type _}
variable (f : X → Y)
variable (g : Y → X)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

example
  (hg : inversa g f)
  : Bijective g :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Para demostrar que \\(g: Y → X\\) es biyectiva, basta probar que existe una
\\(h\\) que es inversa de \\(g\\) por la izquierda y por la derecha; es
decir,
\\begin{align}
   &(∀y ∈ Y)[(h ∘ g)(y) = y] \\tag{1} \\\\
   &(∀x ∈ X)[(g ∘ h)(x) = x] \\tag{2}
\\end{align}

Puesto que \\(g\\) es una inversa de \\(f\\), entonces
\\begin{align}
   &(∀x ∈ X)[(g ∘ f)(x) = x] \\tag{3} \\\\
   &(∀y ∈ Y)[(f ∘ g)(y) = y] \\tag{4}
\\end{align}

Tomando \\(f\\) como \\(h\\), (1) se verifica por (4) y (2) se verifica por (3).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y : Type _}
variable (f : X → Y)
variable (g : Y → X)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

-- 1ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rcases hg with ⟨h1, h2⟩
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  use f
  -- ⊢ LeftInverse f g ∧ Function.RightInverse f g
  constructor
  . -- ⊢ LeftInverse f g
    exact h1
  . -- ⊢ Function.RightInverse f g
    exact h2

-- 2ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rcases hg with ⟨h1, h2⟩
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  use f
  -- ⊢ LeftInverse f g ∧ Function.RightInverse f g
  exact ⟨h1, h2⟩

-- 3ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rcases hg with ⟨h1, h2⟩
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, ⟨h1, h2⟩⟩

-- 4ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  use f
  -- ⊢ LeftInverse f g ∧ Function.RightInverse f g
  exact hg

-- 5ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

-- 6ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  apply bijective_iff_has_inverse.mpr
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

-- Lemas usados
-- ============

-- #check (bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_inversa_de_una_funcion_biyectiva_es_biyectiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_inversa_de_una_funcion_biyectiva_es_biyectiva
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

(* 1ª demostración *)

lemma
  fixes   f :: "'a ⇒ 'b"
  assumes "inversa g f"
  shows   "bij g"
proof (rule bijI)
  show "inj g"
  proof (rule injI)
    fix x y
    assume "g x = g y"
    have h1 : "∀ y. (f ∘ g) y = y"
      by (meson assms inversa_def)
    then have "x = (f ∘ g) x"
      by (simp only: allE)
    also have "… = f (g x)"
      by (simp only: o_apply)
    also have "… = f (g y)"
      by (simp only: ‹g x = g y›)
    also have "… = (f ∘ g) y"
      by (simp only: o_apply)
    also have "… = y"
      using h1 by (simp only: allE)
    finally show "x = y"
      by this
  qed
next
  show "surj g"
  proof (rule surjI)
    fix x
    have h2 : "∀ x. (g ∘ f) x = x"
      by (meson assms inversa_def)
    then have "(g ∘ f) x = x"
      by (simp only: allE)
    then show "g (f x) = x"
      by (simp only: o_apply)
  qed
qed

(* 2ª demostración *)

lemma
  fixes   f :: "'a ⇒ 'b"
  assumes "inversa g f"
  shows   "bij g"
proof (rule bijI)
  show "inj g"
  proof (rule injI)
    fix x y
    assume "g x = g y"
    have h1 : "∀ y. (f ∘ g) y = y"
      by (meson assms inversa_def)
    then show "x = y"
      by (metis ‹g x = g y› o_apply)
  qed
next
  show "surj g"
  proof (rule surjI)
    fix x
    have h2 : "∀ x. (g ∘ f) x = x"
      by (meson assms inversa_def)
    then show "g (f x) = x"
      by (simp only: o_apply)
  qed
qed

end
</pre>
