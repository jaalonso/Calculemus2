---
Título: f[s] \ f[t] ⊆ f[s \ t].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[f[s] \\setminus f[t] ⊆ f[s \\setminus t] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ f[s] \\setminus f[t]\\). Entonces,
\\begin{align}
   &y ∈ f[s] \\tag{1} \\\\
   &y ∉ f[t] \\tag{2}
\\end{align}
Por (1), existe un \\(x\\) tal que
\\begin{align}
   &x ∈ s    \\tag{3} \\\\
   &f(x) = y \\tag{4}
\\end{align}
Por tanto, para demostrar que \\(y ∈ f[s \\setminus t]\\), basta probar que \\(x ∉ t\\). Para ello, supongamos que \\(x ∈ t\\). Entonces, por (4), \\(y ∈ f[t]\\), en contradicción con (2).

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

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s \ f '' t
  -- ⊢ y ∈ f '' (s \ t)
  rcases hy with ⟨yfs, ynft⟩
  -- yfs : y ∈ f '' s
  -- ynft : ¬y ∈ f '' t
  rcases yfs with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  have h1 : x ∉ t := by
    intro xt
    -- xt : x ∈ t
    -- ⊢ False
    have h2 : f x ∈ f '' t := mem_image_of_mem f xt
    have h3 : y ∈ f '' t := by rwa [fxy] at h2
    show False
    exact ynft h3
  have h4 : x ∈ s \ t := mem_diff_of_mem xs h1
  have h5 : f x ∈ f '' (s \ t) := mem_image_of_mem f h4
  show y ∈ f '' (s \ t)
  rwa [fxy] at h5

-- 2ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ f '' s \ f '' t
  -- ⊢ y ∈ f '' (s \ t)
  rcases hy with ⟨yfs, ynft⟩
  -- yfs : y ∈ f '' s
  -- ynft : ¬y ∈ f '' t
  rcases yfs with ⟨x, hx⟩
  -- x : α
  -- hx : x ∈ s ∧ f x = y
  rcases hx with ⟨xs, fxy⟩
  -- xs : x ∈ s
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ s \ t ∧ f x = y
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply ynft
      -- ⊢ y ∈ f '' t
      rw [←fxy]
      -- ⊢ f x ∈ f '' t
      apply mem_image_of_mem
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ f x = y
    exact fxy

-- 3ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
by
  rintro y ⟨⟨x, xs, fxy⟩, ynft⟩
  -- y : β
  -- ynft : ¬y ∈ f '' t
  -- x : α
  -- xs : x ∈ s
  -- fxy : f x = y
  -- ⊢ y ∈ f '' (s \ t)
  use x
  -- ⊢ x ∈ s \ t ∧ f x = y
  aesop

-- 4ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
fun y ⟨⟨x, xs, fxy⟩, ynft⟩ ↦ ⟨x, by aesop⟩

-- 5ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
subset_image_diff f s t

-- Lemmas usados
-- =============

-- variable (x : α)
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
-- #check (subset_image_diff f s t : f '' s \ f '' t ⊆ f '' (s \ t))
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_la_diferencia_de_conjuntos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_la_diferencia_de_conjuntos
imports Main
begin

(* 1ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
proof (rule subsetI)
  fix y
  assume hy : "y ∈ f ` s - f ` t"
  then show "y ∈ f ` (s - t)"
  proof (rule DiffE)
    assume "y ∈ f ` s"
    assume "y ∉ f ` t"
    note ‹y ∈ f ` s›
    then show "y ∈ f ` (s - t)"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x ∈ s"
      have ‹x ∉ t›
      proof (rule notI)
        assume "x ∈ t"
        then have "f x ∈ f ` t"
          by (rule imageI)
        with ‹y = f x› have "y ∈ f ` t"
          by (rule ssubst)
      with ‹y ∉ f ` t› show False
        by (rule notE)
    qed
    with ‹x ∈ s› have "x ∈ s - t"
      by (rule DiffI)
    then have "f x ∈ f ` (s - t)"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` (s - t)"
      by (rule ssubst)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
proof
  fix y
  assume hy : "y ∈ f ` s - f ` t"
  then show "y ∈ f ` (s - t)"
  proof
    assume "y ∈ f ` s"
    assume "y ∉ f ` t"
    note ‹y ∈ f ` s›
    then show "y ∈ f ` (s - t)"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s"
      have ‹x ∉ t›
      proof
        assume "x ∈ t"
        then have "f x ∈ f ` t" by simp
        with ‹y = f x› have "y ∈ f ` t" by simp
      with ‹y ∉ f ` t› show False by simp
    qed
    with ‹x ∈ s› have "x ∈ s - t" by simp
    then have "f x ∈ f ` (s - t)" by simp
    with ‹y = f x› show "y ∈ f ` (s - t)" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
  by (simp only: image_diff_subset)

(* 4ª demostración *)

lemma "f ` s - f ` t ⊆ f ` (s - t)"
  by auto

end
</pre>
