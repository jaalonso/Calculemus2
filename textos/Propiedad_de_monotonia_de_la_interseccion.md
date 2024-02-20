---
Título: Si s ⊆ t, entonces s ∩ u ⊆ t ∩ u
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que "Si \\(s ⊆ t\\), entonces \\(s ∩ u ⊆ t ∩ u\\)".

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set
variable {α : Type}
variable (s t u : Set α)

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ s ∩ u\\). Entonces, se tiene que
\\begin{align}
  &x ∈ s \\tag{1} \\\\
  &x ∈ u \\tag{2}
\\end{align}
De (1) y \\(s ⊆ t\\), se tiene que
\\[ x ∈ t \\tag{3} \\]
De (3) y (2) se tiene que
\\[ x ∈ t ∩ u \\]
que es lo que teníamos que demostrar.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  rw [subset_def]
  -- ⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  intros x h1
  -- x : α
  -- h1 : x ∈ s ∩ u
  -- ⊢ x ∈ t ∩ u
  rcases h1 with ⟨xs, xu⟩
  -- xs : x ∈ s
  -- xu : x ∈ u
  constructor
  . -- ⊢ x ∈ t
    rw [subset_def] at h
    -- h : ∀ (x : α), x ∈ s → x ∈ t
    apply h
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ u
    exact xu

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  rw [subset_def]
  -- ⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  rintro x ⟨xs, xu⟩
  -- x : α
  -- xs : x ∈ s
  -- xu : x ∈ u
  rw [subset_def] at h
  -- h : ∀ (x : α), x ∈ s → x ∈ t
  exact ⟨h x xs, xu⟩

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  simp only [subset_def]
  -- ⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  rintro x ⟨xs, xu⟩
  -- x : α
  -- xs : x ∈ s
  -- xu : x ∈ u
  rw [subset_def] at h
  -- h : ∀ (x : α), x ∈ s → x ∈ t
  exact ⟨h _ xs, xu⟩

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  intros x xsu
  -- x : α
  -- xsu : x ∈ s ∩ u
  -- ⊢ x ∈ t ∩ u
  exact ⟨h xsu.1, xsu.2⟩

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by
  rintro x ⟨xs, xu⟩
  -- xs : x ∈ s
  -- xu : x ∈ u
  -- ⊢ x ∈ t ∩ u
  exact ⟨h xs, xu⟩

-- 6ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦  ⟨h xs, xu⟩

-- 7ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter_left u h

-- Lema usado
-- ==========

-- #check (inter_subset_inter_left u : s ⊆ t → s ∩ u ⊆ t ∩ u)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_de_monotonia_de_la_interseccion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Propiedad_de_monotonia_de_la_interseccion
imports Main
begin

(* 1ª solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
proof (rule subsetI)
  fix x
  assume hx: "x ∈ s ∩ u"
  have xs: "x ∈ s"
    using hx
    by (simp only: IntD1)
  then have xt: "x ∈ t"
    using assms
    by (simp only: subset_eq)
  have xu: "x ∈ u"
    using hx
    by (simp only: IntD2)
  show "x ∈ t ∩ u"
    using xt xu
    by (simp only: Int_iff)
qed

(* 2 solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
proof
  fix x
  assume hx: "x ∈ s ∩ u"
  have xs: "x ∈ s"
    using hx
    by simp
  then have xt: "x ∈ t"
    using assms
    by auto
  have xu: "x ∈ u"
    using hx
    by simp
  show "x ∈ t ∩ u"
    using xt xu
    by simp
qed

(* 3ª solución *)
lemma
  assumes "s ⊆ t"
  shows   "s ∩ u ⊆ t ∩ u"
using assms
by auto

(* 4ª solución *)
lemma
  "s ⊆ t ⟹ s ∩ u ⊆ t ∩ u"
by auto

end
</pre>
