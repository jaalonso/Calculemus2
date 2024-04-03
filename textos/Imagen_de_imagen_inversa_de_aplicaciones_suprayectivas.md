---
Título: Si f es suprayectiva, entonces u ⊆ f[f⁻¹[u]].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) es suprayectiva, entonces
\\[ u ⊆ f[f⁻¹[u]] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set Function
variable {α β : Type _}
variable (f : α → β)
variable (u : Set β)

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ u\\). Por ser \\(f\\) suprayectiva, exite un \\(x\\) tal que
\\[ f(x) = y \\tag{1} \\]
Por tanto, \\(x ∈ f⁻¹[u]\\) y
\\[ f(x) ∈ f[f⁻¹[u]] \\tag{2} \\]
Finalmente, por (1) y (2),
\\[ y ∈ f[f⁻¹[u]] \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set Function
variable {α β : Type _}
variable (f : α → β)
variable (u : Set β)

-- 1ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ f ⁻¹' u ∧ f x = y
  constructor
  { -- ⊢ x ∈ f ⁻¹' u
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u
    rw [fxy]
    -- ⊢ y ∈ u
    exact yu }
  { -- ⊢ f x = y
    exact fxy }

-- 2ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  use x
  -- ⊢ x ∈ f ⁻¹' u ∧ f x = y
  constructor
  { show f x ∈ u
    rw [fxy]
    -- ⊢ y ∈ u
    exact yu }
  { show f x = y
    exact fxy }

-- 3ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- #check (mem_preimage : x ∈ f ⁻¹' u ↔ f x ∈ u)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
proof (rule subsetI)
  fix y
  assume "y ∈ u"
  have "∃x. y = f x"
    using ‹surj f› by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x ∈ u"
    using ‹y ∈ u› by (rule subst)
  then have "x ∈ f -` u"
    by (simp only: vimage_eq)
  then have "f x ∈ f ` (f -` u)"
    by (rule imageI)
  with ‹y = f x› show "y ∈ f ` (f -` u)"
    by (rule ssubst)
qed

(* 2ª demostración *)
lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
proof
  fix y
  assume "y ∈ u"
  have "∃x. y = f x"
    using ‹surj f› by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x ∈ u"
    using ‹y ∈ u› by simp
  then have "x ∈ f -` u"
    by simp
  then have "f x ∈ f ` (f -` u)"
    by simp
  with ‹y = f x› show "y ∈ f ` (f -` u)"
    by simp
qed

(* 3ª demostración *)
lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
  using assms
  by (simp only: surj_image_vimage_eq)

(* 4ª demostración *)
lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
  using assms
  unfolding surj_def
  by auto

(* 5ª demostración *)
lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
  using assms
  by auto

end
</pre>
