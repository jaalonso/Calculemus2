---
Título: f[s ∩ t] ⊆ f[s] ∩ f[t]
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ f[s ∩ t] ⊆ f[s] ∩ f[t]​ \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea tal que
\\[ y ∈ f[s ∩ t] \\]
Por tanto, existe un \\(x\\) tal que
\\begin{align}
  x ∈ s ∩ t  \\tag{1} \\\\
  f(x) = y   \\tag{2}
\\end{align}
Por (1), se tiene que
\\begin{align}
  x ∈ s      \\tag{3} \\\\
  x ∈ t      \\tag{4}
\\end{align}
Por (2) y (3), se tiene
\\[ y ∈ f[s] \\tag{5} \\]
Por (2) y (4), se tiene
\\[ y ∈ f[t] \\tag{6} \\]
Por (5) y (6), se tiene
\\[ y ∈ f[s] ∩ f[t] \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' (s ∩ t)
  -- ⊢ y ∈ f '' s ∩ f '' t
  rcases hy with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∩ t ∧ f x = y
  rcases hx with ⟨xst, fxy⟩
  -- xst : x ∈ s ∩ t
  -- fxy : f x = y
  constructor
  . -- ⊢ y ∈ f '' s
    use x
    -- ⊢ x ∈ s ∧ f x = y
    constructor
    . -- ⊢ x ∈ s
      exact xst.1
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' t
    use x
    -- ⊢ x ∈ t ∧ f x = y
    constructor
    . -- ⊢ x ∈ t
      exact xst.2
    . -- ⊢ f x = y
      exact fxy

-- 2ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' (s ∩ t)
  -- ⊢ y ∈ f '' s ∩ f '' t
  rcases hy with ⟨x, ⟨xs, xt⟩, fxy⟩
  -- x : α
  -- fxy : f x = y
  -- xs : x ∈ s
  -- xt : x ∈ t
  constructor
  . -- ⊢ y ∈ f '' s
    use x
    -- ⊢ x ∈ s ∧ f x = y
    exact ⟨xs, fxy⟩
  . -- ⊢ y ∈ f '' t
    use x
    -- ⊢ x ∈ t ∧ f x = y
    exact ⟨xt, fxy⟩

-- 3ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
image_inter_subset f s t

-- 4ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by intro ; aesop

-- Lemas usados
-- ============

-- #check (image_inter_subset f s t : f '' (s ∩ t) ⊆ f '' s ∩ f '' t)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_la_interseccion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_la_interseccion
imports Main
begin

(* 1ª demostración *)

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (s ∩ t)"
  then have "y ∈ f ` s"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ s"
      using ‹x ∈ s ∩ t› by (rule IntD1)
    then have "f x ∈ f ` s"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` s"
      by (rule ssubst)
  qed
  moreover
  note ‹y ∈ f ` (s ∩ t)›
  then have "y ∈ f ` t"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ t"
      using ‹x ∈ s ∩ t› by (rule IntD2)
    then have "f x ∈ f ` t"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` t"
      by (rule ssubst)
  qed
  ultimately show "y ∈ f ` s ∩ f ` t"
    by (rule IntI)
qed

(* 2ª demostración *)

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
proof
  fix y
  assume "y ∈ f ` (s ∩ t)"
  then have "y ∈ f ` s"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ s"
      using ‹x ∈ s ∩ t› by simp
    then have "f x ∈ f ` s"
      by simp
    with ‹y = f x› show "y ∈ f ` s"
      by simp
  qed
  moreover
  note ‹y ∈ f ` (s ∩ t)›
  then have "y ∈ f ` t"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∩ t"
    have "x ∈ t"
      using ‹x ∈ s ∩ t› by simp
    then have "f x ∈ f ` t"
      by simp
    with ‹y = f x› show "y ∈ f ` t"
      by simp
  qed
  ultimately show "y ∈ f ` s ∩ f ` t"
    by simp
qed

(* 3ª demostración *)

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
proof
  fix y
  assume "y ∈ f ` (s ∩ t)"
  then obtain x where hx : "y = f x ∧ x ∈ s ∩ t" by auto
  then have "y = f x" by simp
  have "x ∈ s" using hx by simp
  have "x ∈ t" using hx by simp
  have "y ∈  f ` s" using ‹y = f x› ‹x ∈ s› by simp
  moreover
  have "y ∈  f ` t" using ‹y = f x› ‹x ∈ t› by simp
  ultimately show "y ∈ f ` s ∩ f ` t"
    by simp
qed

(* 4ª demostración *)

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
  by (simp only: image_Int_subset)

(* 5ª demostración *)

lemma "f ` (s ∩ t) ⊆ f ` s ∩ f ` t"
  by auto

end
</pre>
