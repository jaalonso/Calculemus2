---
Título: f[f⁻¹[u]] ⊆ u
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ f[f⁻¹[u]] ⊆ u \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set

variable {α β : Type _}
variable (f : α → β)
variable (u : Set β)

example : f '' (f⁻¹' u) ⊆ u :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ f[f⁻¹[u]]\\). Entonces existe un \\(x\\) tal que
\\begin{align}
   &x ∈ f⁻¹[u] \\tag{1} \\\\
   &f(x) = y   \\tag{2}
\\end{align}
Por (1),
\\[ f(x) ∈ u \\]
y, por (2),
\\[ y ∈ u \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set

variable {α β : Type _}
variable (f : α → β)
variable (u : Set β)

-- 1ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  obtain ⟨x : α, h1 : x ∈ f ⁻¹' u ∧ f x = y⟩ := h
  obtain ⟨hx : x ∈ f ⁻¹' u, fxy : f x = y⟩ := h1
  have h2 : f x ∈ u := mem_preimage.mp hx
  show y ∈ u
  exact fxy ▸ h2

-- 2ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  rcases h with ⟨x, h2⟩
  -- x : α
  -- h2 : x ∈ f ⁻¹' u ∧ f x = y
  rcases h2 with ⟨hx, fxy⟩
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 3ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  intros y h
  -- y : β
  -- h : y ∈ f '' (f ⁻¹' u)
  -- ⊢ y ∈ u
  rcases h with ⟨x, hx, fxy⟩
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 4ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  rintro y ⟨x, hx, fxy⟩
  -- y : β
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- fxy : f x = y
  -- ⊢ y ∈ u
  rw [←fxy]
  -- ⊢ f x ∈ u
  exact hx

-- 5ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by
  rintro y ⟨x, hx, rfl⟩
  -- x : α
  -- hx : x ∈ f ⁻¹' u
  -- ⊢ f x ∈ u
  exact hx

-- 6ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
image_preimage_subset f u

-- Lemas usados
-- ============

-- #check (image_preimage_subset f u : f '' (f⁻¹' u) ⊆ u)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_la_imagen_inversa.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_la_imagen_inversa
imports Main
begin

(* 1ª demostración *)

lemma "f ` (f -` u) ⊆ u"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (f -` u)"
  then show "y ∈ u"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ f -` u"
    then have "f x ∈ u"
      by (rule vimageD)
    with ‹y = f x› show "y ∈ u"
      by (rule ssubst)
  qed
qed

(* 2ª demostración *)

lemma "f ` (f -` u) ⊆ u"
proof
  fix y
  assume "y ∈ f ` (f -` u)"
  then show "y ∈ u"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ f -` u"
    then have "f x ∈ u"
      by simp
    with ‹y = f x› show "y ∈ u"
      by simp
  qed
qed

(* 3ª demostración *)

lemma "f ` (f -` u) ⊆ u"
  by (simp only: image_vimage_subset)

(* 4ª demostración *)

lemma "f ` (f -` u) ⊆ u"
  by auto

end
</pre>
