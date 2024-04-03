---
Título: Si s ⊆ t, entonces f[s] ⊆ f[t].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(s ⊆ t\\), entonces \\(f[s] ⊆ f[t]\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ f[s]\\). Entonces, existe un x tal que
\\begin{align}
   &x ∈ s    \\tag{1} \\\\
   &f(x) = y \\tag{2}
\\end{align}
Por (1) y la hipótesis,
\\[ x ∈ t \\tag{3} \\]
Por (3),
\\[ f(x) ∈ f[t] \\tag{4} \\]
y, por (2) y (4),
\\[ y ∈ f[t] \\]

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

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s
  -- ⊢ y ∈ f '' t
  rw [mem_image] at hy
  -- hy : ∃ x, x ∈ s ∧ f x = y
  rcases hy with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ t ∧ f x = y
  constructor
  . -- ⊢ x ∈ t
    exact h xs
  . -- ⊢ f x = y
    exact fxy

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s
  -- ⊢ y ∈ f '' t
  rcases hy with ⟨x, xs, fxy⟩
  -- x : α
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ t ∧ f x = y
  exact ⟨h xs, fxy⟩

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
image_subset f h

-- Lemas usados
-- ============

-- variable (y : β)
-- #check (mem_image f s y : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y)
-- #check (image_subset f : s ⊆ t → f '' s ⊆ f '' t)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Monotonia_de_la_imagen_de_conjuntos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Monotonia_de_la_imagen_de_conjuntos
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` s"
  then show "y ∈ f ` t"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s"
    then have "x ∈ t"
      using ‹s ⊆ t› by (simp only: set_rev_mp)
    then have "f x ∈ f ` t"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` t"
      by (rule ssubst)
  qed
qed

(* 2ª demostración *)
lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
proof
  fix y
  assume "y ∈ f ` s"
  then show "y ∈ f ` t"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s"
    then have "x ∈ t"
      using ‹s ⊆ t› by (simp only: set_rev_mp)
    then have "f x ∈ f ` t"
      by simp
    with ‹y = f x› show "y ∈ f ` t"
      by simp
  qed
qed

(* 3ª demostración *)
lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
  using assms
  by blast

(* 4ª demostración *)
lemma
  assumes "s ⊆ t"
  shows "f ` s ⊆ f ` t"
  using assms
  by (simp only: image_mono)

end
</pre>
