---
title: Si g ∘ f es inyectiva, entonces f es inyectiva
date: 2024-06-07 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Sean \\(f: X → Y\\) y \\(g: Y → Z\\). Demostrar con Lean4 que si \\(g ∘ f\\) es inyectiva, entonces \\(f\\) es inyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

example
  (h : Injective (g ∘ f))
  : Injective f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(a, b ∈ X\\) tales que
\\[ f(a) = f(b) \\]
Entonces,
\\[ g(f(a)) = g(f(b)) \\]
Luego
\\[ (g ∘ f)(a) = (g ∘ f)(b) \\]
y, como g ∘ f es inyectiva,
\\[ a = b \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (h : Injective (g ∘ f))
  : Injective f :=
by
  intro a b hab
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  have h1 : (g ∘ f) a = (g ∘ f) b := by simp_all only [comp_apply]
  exact h h1

-- 2ª demostración
-- ===============

example
  (h : Injective (g ∘ f))
  : Injective f :=
by
  intro a b hab
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  apply h
  -- ⊢ (g ∘ f) a = (g ∘ f) b
  change g (f a) = g (f b)
  -- ⊢ g (f a) = g (f b)
  rw [hab]

-- Lemas usados
-- ============

-- variable (x : X)
-- #check (Function.comp_apply : (g ∘ f) x = g (f x))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Inyectiva_si_lo_es_la_composicion.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Inyectiva_si_lo_es_la_composicion
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "inj (g ∘ f)"
  shows "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  show "x = y"
  proof -
    have "g (f x) = g (f y)"
      using ‹f x = f y›
      by simp
    then have "(g ∘ f) x = (g ∘ f) y"
      by simp
    with assms show "x = y"
      by (rule injD)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "inj (g ∘ f)"
  shows "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  then show "x = y"
    using assms injD by fastforce
qed

(* 3ª demostración *)

lemma
  assumes "inj (g ∘ f)"
  shows "inj f"
using assms
by (rule inj_on_imageI2)

(* Nota: Al calcular el cursor en shows sale una sugerencia indicando
   que se puede demostrar con la regla inj_on_imageI2. *)

end
</pre>
