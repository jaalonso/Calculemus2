---
Título: f[s] ⊆ u ↔ s ⊆ f⁻¹[u]
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ f[s] ⊆ u ↔ s ⊆ f⁻¹[u] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
open Set
variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (u : Set β)

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Los demostraremos probando las dos implicaciones.

(⟹) Supongamos que
\\[ f[s] ⊆ u \\tag{1} \\]
y tenemos que demostrar que
\\[ s ⊆ f⁻¹[u] \\]
Se prueba mediante las siguientes implicaciones
\\begin{align}
   x ∈ s &⟹ f(x) ∈ f[s] \\\\
         &⟹ f(x) ∈ u    &&\\text{[por (1)]} \\\\
         &⟹ x ∈ f⁻¹[u]
\\end{align}

(⟸) Supongamos que
\\[ s ⊆ f⁻¹[u] \\tag{2} \\]
y tenemos que demostrar que
\\[ f[s] ⊆ u \\]
Para ello, sea \\(y ∈ f[s]\\). Entonces, existe un
\\[ x ∈ s \\tag{3} \\]
tal que
\\[ y = f(x) \\tag{4} \\]
Entonces,
\\begin{align}
       &x ∈ f⁻¹[u] &&\\text{[por (2) y (3)]} \\\\
   ⟹ &f(x) ∈ u   \\\\
   ⟹ &y ∈ u      &&\\text{[por (4)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (u : Set β)

-- 1ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
calc f '' s ⊆ u
   ↔ ∀ y, y ∈ f '' s → y ∈ u :=
       by simp only [subset_def]
 _ ↔ ∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u :=
       by simp only [mem_image]
 _ ↔ ∀ x, x ∈ s → f x ∈ u := by
       constructor
       . -- (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u) → (∀ x, x ∈ s → f x ∈ u)
         intro h x xs
         -- h : ∀ (y : β), (∃ x, x ∈ s ∧ f x = y) → y ∈ u
         -- x : α
         -- xs : x ∈ s
         -- ⊢ f x ∈ u
         exact h (f x) (by use x, xs)
       . -- (∀ x, x ∈ s → f x ∈ u) → (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u)
         intro h y hy
         -- h : ∀ (x : α), x ∈ s → f x ∈ u
         -- y : β
         -- hy : ∃ x, x ∈ s ∧ f x = y
         -- ⊢ y ∈ u
         obtain ⟨x, hx⟩ := hy
         -- x : α
         -- hx : x ∈ s ∧ f x = y
         have h1 : y = f x := hx.2.symm
         have h2 : f x ∈ u := h x hx.1
         show y ∈ u
         exact mem_of_eq_of_mem h1 h2
 _ ↔ ∀ x, x ∈ s → x ∈ f ⁻¹' u :=
       by simp only [mem_preimage]
 _ ↔ s ⊆ f ⁻¹' u :=
       by simp only [subset_def]

-- 2ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
calc f '' s ⊆ u
   ↔ ∀ y, y ∈ f '' s → y ∈ u :=
       by simp only [subset_def]
 _ ↔ ∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u :=
       by simp only [mem_image]
 _ ↔ ∀ x, x ∈ s → f x ∈ u := by
       constructor
       . -- (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u) → (∀ x, x ∈ s → f x ∈ u)
         intro h x xs
         -- h : ∀ (y : β), (∃ x, x ∈ s ∧ f x = y) → y ∈ u
         -- x : α
         -- xs : x ∈ s
         -- ⊢ f x ∈ u
         apply h (f x)
         -- ⊢ ∃ x_1, x_1 ∈ s ∧ f x_1 = f x
         use x, xs
       . -- (∀ x, x ∈ s → f x ∈ u) → (∀ y, (∃ x, x ∈ s ∧ f x = y) → y ∈ u)
         intro h y hy
         -- h : ∀ (x : α), x ∈ s → f x ∈ u
         -- y : β
         -- hy : ∃ x, x ∈ s ∧ f x = y
         -- ⊢ y ∈ u
         obtain ⟨x, hx⟩ := hy
         -- x : α
         -- hx : x ∈ s ∧ f x = y
         rw [←hx.2]
         -- ⊢ f x ∈ u
         apply h x
         -- ⊢ x ∈ s
         exact hx.1
 _ ↔ ∀ x, x ∈ s → x ∈ f ⁻¹' u :=
       by simp only [mem_preimage]
 _ ↔ s ⊆ f ⁻¹' u :=
       by simp only [subset_def]

-- 3ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by
  constructor
  . -- ⊢ f '' s ⊆ u → s ⊆ f ⁻¹' u
    intros h x xs
    -- h : f '' s ⊆ u
    -- x : α
    -- xs : x ∈ s
    -- ⊢ x ∈ f ⁻¹' u
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u
    apply h
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ s ⊆ f ⁻¹' u → f '' s ⊆ u
    intros h y hy
    -- h : s ⊆ f ⁻¹' u
    -- y : β
    -- hy : y ∈ f '' s
    -- ⊢ y ∈ u
    rcases hy with ⟨x, xs, fxy⟩
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    rw [←fxy]
    -- ⊢ f x ∈ u
    exact h xs

-- 4ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by
  constructor
  . -- ⊢ f '' s ⊆ u → s ⊆ f ⁻¹' u
    intros h x xs
    -- h : f '' s ⊆ u
    -- x : α
    -- xs : x ∈ s
    -- ⊢ x ∈ f ⁻¹' u
    apply h
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ s ⊆ f ⁻¹' u → f '' s ⊆ u
    rintro h y ⟨x, xs, rfl⟩
    -- h : s ⊆ f ⁻¹' u
    -- x : α
    -- xs : x ∈ s
    -- ⊢ f x ∈ u
    exact h xs

-- 5ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
image_subset_iff

-- 4ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by simp

-- Lemas usados
-- ============

-- variable (x y : α)
-- #check (image_subset_iff : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (mem_of_eq_of_mem : x = y → y ∈ s → x ∈ s)
-- #check (mem_preimage : x ∈ f ⁻¹' u ↔ f x ∈ u)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Subconjunto_de_la_imagen_inversa.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Subconjunto_de_la_imagen_inversa
imports Main
begin

(* 1ª demostración *)
lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
proof (rule iffI)
  assume "f ` s ⊆ u"
  show "s ⊆ f -` u"
  proof (rule subsetI)
    fix x
    assume "x ∈ s"
    then have "f x ∈ f ` s"
      by (simp only: imageI)
    then have "f x ∈ u"
      using ‹f ` s ⊆ u› by (rule set_rev_mp)
    then show "x ∈ f -` u"
      by (simp only: vimageI)
  qed
next
  assume "s ⊆ f -` u"
  show "f ` s ⊆ u"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` s"
    then show "y ∈ u"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s"
      then have "x ∈ f -` u"
        using ‹s ⊆ f -` u› by (rule set_rev_mp)
      then have "f x ∈ u"
        by (rule vimageD)
      with ‹y = f x› show "y ∈ u"
        by (rule ssubst)
    qed
  qed
qed

(* 2ª demostración *)
lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
proof
  assume "f ` s ⊆ u"
  show "s ⊆ f -` u"
  proof
    fix x
    assume "x ∈ s"
    then have "f x ∈ f ` s"
      by simp
    then have "f x ∈ u"
      using ‹f ` s ⊆ u› by (simp add: set_rev_mp)
    then show "x ∈ f -` u"
      by simp
  qed
next
  assume "s ⊆ f -` u"
  show "f ` s ⊆ u"
  proof
    fix y
    assume "y ∈ f ` s"
    then show "y ∈ u"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s"
      then have "x ∈ f -` u"
        using ‹s ⊆ f -` u› by (simp only: set_rev_mp)
      then have "f x ∈ u"
        by simp
      with ‹y = f x› show "y ∈ u"
        by simp
    qed
  qed
qed

(* 3ª demostración *)
lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
  by (simp only: image_subset_iff_subset_vimage)

(* 4ª demostración *)
lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
  by auto

end
</pre>
