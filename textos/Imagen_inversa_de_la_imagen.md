---
Título: s ⊆ f⁻¹[f[s]​]
Autor:  José A. Alonso
---

[mathjax]

Demostrar que si \\(s\\) es un subconjunto del dominio de la función \\(f\\), entonces \\(s\\) está contenido en la imagen inversa de la imagen de \\(s\\) por \\(f\\); es decir,
\\[ s ⊆ f⁻¹[f[s]] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set
variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)

example : s ⊆ f ⁻¹' (f '' s) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se demuestra mediante la siguiente cadena de implicaciones
\\begin{align}
   x ∈ s &⟹ f(x) ∈ f[s] \\\\
         &⟹ x ∈ f⁻¹[f[s]]
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)

-- 1ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  have h1 : f x ∈ f '' s := mem_image_of_mem f xs
  show x ∈ f ⁻¹' (f '' s)
  exact mem_preimage.mp h1

-- 2ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  apply mem_preimage.mpr
  -- ⊢ f x ∈ f '' s
  apply mem_image_of_mem
  -- ⊢ x ∈ s
  exact xs

-- 3ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  apply mem_image_of_mem
  -- ⊢ x ∈ s
  exact xs

-- 4ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
fun _ ↦ mem_image_of_mem f

-- 5ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  show f x ∈ f '' s
  use x, xs

-- 6ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
by
  intros x xs
  -- x : α
  -- xs : x ∈ s
  -- ⊢ x ∈ f ⁻¹' (f '' s)
  use x, xs

-- 7ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
subset_preimage_image f s

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set β)
-- #check (mem_preimage : x ∈ f ⁻¹' t ↔ f x ∈ t)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (subset_preimage_image f s : s ⊆ f ⁻¹' (f '' s))
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_inversa_de_la_imagen.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_inversa_de_la_imagen
imports Main
begin

(* 1ª demostración *)
lemma "s ⊆ f -` (f ` s)"
proof (rule subsetI)
  fix x
  assume "x ∈ s"
  then have "f x ∈ f ` s"
    by (simp only: imageI)
  then show "x ∈ f -` (f ` s)"
    by (simp only: vimageI)
qed

(* 2ª demostración *)
lemma "s ⊆ f -` (f ` s)"
proof
  fix x
  assume "x ∈ s"
  then have "f x ∈ f ` s" by simp
  then show "x ∈ f -` (f ` s)" by simp
qed

(* 3ª demostración *)
lemma "s ⊆ f -` (f ` s)"
  by auto

end
</pre>
