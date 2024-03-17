---
Título: Si f es inyectiva, entonces f⁻¹[f[s]​] ⊆ s
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) es inyectiva, entonces \\(f⁻¹[f[s]​] ⊆ s\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set Function
variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x\\) tal que
\\[ x ∈ f⁻¹[f[s]] \\]
Entonces,
\\[ f(x) ∈ f[s] \\]
y, por tanto, existe un
\\[ y ∈ s \\tag{1} \\]
tal que
\\[ f(y) = f(x) \\tag{2} \\]
De (2), puesto que \\(f\\) es inyectiva, se tiene que
\\[ y = x \\tag{3} \\]
Finalmente, de (3) y (1), se tiene que
\\[ x ∈ s \\]
que es lo que teníamos que demostrar.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set Function

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)

-- 1ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  have h1 : f x ∈ f '' s := mem_preimage.mp hx
  have h2 : ∃ y, y ∈ s ∧ f y = f x := (mem_image f s (f x)).mp h1
  obtain ⟨y, hy : y ∈ s ∧ f y = f x⟩ := h2
  obtain ⟨ys : y ∈ s, fyx : f y = f x⟩ := hy
  have h3 : y = x := h fyx
  show x ∈ s
  exact h3 ▸ ys

-- 2ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  rw [mem_preimage] at hx
  -- hx : f x ∈ f '' s
  rw [mem_image] at hx
  -- hx : ∃ x_1, x_1 ∈ s ∧ f x_1 = f x
  rcases hx with ⟨y, hy⟩
  -- y : α
  -- hy : y ∈ s ∧ f y = f x
  rcases hy with ⟨ys, fyx⟩
  -- ys : y ∈ s
  -- fyx : f y = f x
  unfold Injective at h
  -- h : ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
  have h1 : y = x := h fyx
  rw [←h1]
  -- ⊢ y ∈ s
  exact ys

-- 3ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ f ⁻¹' (f '' s)
  -- ⊢ x ∈ s
  rw [mem_preimage] at hx
  -- hx : f x ∈ f '' s
  rcases hx with ⟨y, ys, fyx⟩
  -- y : α
  -- ys : y ∈ s
  -- fyx : f y = f x
  rw [←h fyx]
  -- ⊢ y ∈ s
  exact ys

-- 4ª demostración
-- ===============

example
  (h : Injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
by
  rintro x ⟨y, ys, hy⟩
  -- x y : α
  -- ys : y ∈ s
  -- hy : f y = f x
  -- ⊢ x ∈ s
  rw [←h hy]
  -- ⊢ y ∈ s
  exact ys

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (y : β)
-- variable (t : Set β)
-- #check (mem_image f s y : y ∈ f '' s ↔ ∃ (x : α), x ∈ s ∧ f x = y)
-- #check (mem_preimage : x ∈ f ⁻¹' t ↔ f x ∈ t)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
proof (rule subsetI)
  fix x
  assume "x ∈ f -` (f ` s)"
  then have "f x ∈ f ` s"
    by (rule vimageD)
  then show "x ∈ s"
  proof (rule imageE)
    fix y
    assume "f x = f y"
    assume "y ∈ s"
    have "x = y"
      using ‹inj f› ‹f x = f y› by (rule injD)
    then show "x ∈ s"
      using ‹y ∈ s›  by (rule ssubst)
  qed
qed

(* 2ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
proof
  fix x
  assume "x ∈ f -` (f ` s)"
  then have "f x ∈ f ` s"
    by simp
  then show "x ∈ s"
  proof
    fix y
    assume "f x = f y"
    assume "y ∈ s"
    have "x = y"
      using ‹inj f› ‹f x = f y› by (rule injD)
    then show "x ∈ s"
      using ‹y ∈ s›  by simp
  qed
qed

(* 3ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
  using assms
  unfolding inj_def
  by auto

(* 4ª demostración *)
lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
  using assms
  by (simp only: inj_vimage_image_eq)

end
</pre>
