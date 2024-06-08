---
title: Si g ∘ f es suprayectiva, entonces g es suprayectiva.
date: 2024-06-10 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Sean \\(f: X → Y\\) y \\(g: Y → Z\\). Demostrar que si \\(g ∘ f\\) es suprayectiva, entonces \\(g\\) es suprayectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

example
  (h : Surjective (g ∘ f))
  : Surjective g :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se \\(z ∈ Z\\). Entonces, por ser \\(g ∘ f\\) suprayectiva, existe un \\(x ∈ X\\) tal
que
\\[ (g ∘ f)(x) = z \\tag{1} \\]
Por tanto, existe \\(y = f(x) ∈ Y\\) tal que
\\begin{align}
   g(y) &= g(f(x))       \\\\
        &= (g ∘ f)(x)    \\\\
        &= z             &&\\text{[por (1)]}
\\end{align}

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
  (h : Surjective (g ∘ f))
  : Surjective g :=
by
  intro z
  -- z : Z
  -- ⊢ ∃ a, g a = z
  cases' h z with x hx
  -- x : X
  -- hx : (g ∘ f) x = z
  use f x
  -- ⊢ g (f x) = z
  exact hx

-- 2ª demostración
-- ===============

example
  (h : Surjective (g ∘ f))
  : Surjective g :=
by
  intro z
  -- z : Z
  -- ⊢ ∃ a, g a = z
  cases' h z with x hx
  -- x : X
  -- hx : (g ∘ f) x = z
  exact ⟨f x, hx⟩
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suprayectiva_si_lo_es_la_composicion.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Suprayectiva_si_lo_es_la_composicion
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "surj (g ∘ f)"
  shows "surj g"
proof (unfold Fun.surj_def, rule)
  fix z
  have "∃x. z = (g ∘ f) x"
    using assms
    by (rule surjD)
  then obtain x where "z = (g ∘ f) x"
    by (rule exE)
  then have "z = g (f x)"
    by (simp only: Fun.comp_apply)
  then show "∃y. z = g y"
    by (rule exI)
qed

(* 2 demostración *)

lemma
  assumes "surj (g ∘ f)"
  shows "surj g"
using assms
by auto

end
</pre>
