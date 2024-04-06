---
Título: Si u ⊆ v, entonces f⁻¹[u] ⊆ f⁻¹[v].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(u ⊆ v\\), entonces \\(f⁻¹[u] ⊆ f⁻¹[v]\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set

variable {α β : Type _}
variable (f : α → β)
variable (u v : Set β)

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por la siguiente cadena de implicaciones:
\\begin{align}
   x ∈ f⁻¹[u] &⟹ f(x) ∈ u \\\\
              &⟹ f(x) ∈ v      &&\\text{[porque \\(u ⊆ v\\)]} \\\\
              &⟹ x ∈ f⁻¹[v]
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set

variable {α β : Type _}
variable (f : α → β)
variable (u v : Set β)

-- 1ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  have h1 : f x ∈ u := mem_preimage.mp hx
  have h2 : f x ∈ v := h h1
  show x ∈ f ⁻¹' v
  exact mem_preimage.mpr h2

-- 2ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  apply mem_preimage.mpr
  -- ⊢ f x ∈ v
  apply h
  -- ⊢ f x ∈ u
  apply mem_preimage.mp
  -- ⊢ x ∈ f ⁻¹' u
  exact hx

-- 3ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  apply h
  -- ⊢ f x ∈ u
  exact hx

-- 4ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ x ∈ f ⁻¹' v
  exact h hx

-- 5ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
fun _ hx ↦ h hx

-- 6ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

-- 7ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
preimage_mono h

-- 8ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by tauto

-- Lemas usados
-- ============

-- variable (a : α)
-- #check (mem_preimage : a ∈ f ⁻¹' u ↔ f a ∈ u)
-- #check (preimage_mono : u ⊆ v → f ⁻¹' u ⊆ f ⁻¹' v)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Monotonia_de_la_imagen_inversa.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Monotonia_de_la_imagen_inversa
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
proof (rule subsetI)
  fix x
  assume "x ∈ f -` u"
  then have "f x ∈ u"
    by (rule vimageD)
  then have "f x ∈ v"
    using ‹u ⊆ v› by (rule set_rev_mp)
  then show "x ∈ f -` v"
    by (simp only: vimage_eq)
qed

(* 2ª demostración *)
lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
proof
  fix x
  assume "x ∈ f -` u"
  then have "f x ∈ u"
    by simp
  then have "f x ∈ v"
    using ‹u ⊆ v› by (rule set_rev_mp)
  then show "x ∈ f -` v"
    by simp
qed

(* 3ª demostración *)
lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
  using assms
  by (simp only: vimage_mono)

(* 4ª demostración *)
lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
  using assms
  by blast

end
</pre>
