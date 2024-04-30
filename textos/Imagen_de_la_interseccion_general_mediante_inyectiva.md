---
title: Imagen de la interseccion general mediante aplicaciones inyectivas
date: 2024-04-29 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(f\\) es inyectiva, entonces
\\[⋂ᵢf[Aᵢ] ⊆ f\left[⋂ᵢAᵢ\right] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set Function

variable {α β I : Type _}
variable (f : α → β)
variable (A : I → Set α)

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ ⋂ᵢf[Aᵢ]\\). Entonces,
\\begin{align}
   & (∀i ∈ I)y ∈ f[Aᵢ]  \\tag{1} \\\\
   & y ∈ f[Aᵢ]
\\end{align}
Por tanto, existe un \\(x ∈ Aᵢ\\) tal que
\\[ f(x) = y \\tag{2} \\]

Veamos que \\(x ∈ ⋂ᵢAᵢ\\). Para ello, sea \\(j ∈ I\\). Por (1),
\\[ y ∈ f[Aⱼ] \\]
Luego, existe un \\(z\\) tal que
\\begin{align}
   &z ∈ Aⱼ    \\tag{3} \\\\
   &f(z) = y
\\end{align}
Pot (2),
\\[ f(x) = f(z) \\]
y, por ser \\(f\\) inyectiva,
\\[ x = z \\]
y, por (3),
\\[ x ∈ Aⱼ \\]

Puesto que \\(x ∈ ⋂ᵢAᵢ\\) se tiene que \\(f(x) ∈ f\left[⋂ᵢAᵢ\right]\\) y, por (2), \\(y ∈ f\left[⋂ᵢAᵢ\right]\\).


<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set Function

variable {α β I : Type _}
variable (f : α → β)
variable (A : I → Set α)

-- 1ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ ⋂ (i : I), f '' A i
  -- ⊢ y ∈ f '' ⋂ (i : I), A i
  have h1 : ∀ (i : I), y ∈ f '' A i := mem_iInter.mp hy
  have h2 : y ∈ f '' A i := h1 i
  obtain ⟨x : α, h3 : x ∈ A i ∧ f x = y⟩ := h2
  have h4 : f x = y := h3.2
  have h5 : ∀ i : I, x ∈ A i := by
    intro j
    have h5a : y ∈ f '' A j := h1 j
    obtain ⟨z : α, h5b : z ∈ A j ∧ f z = y⟩ := h5a
    have h5c : z ∈ A j := h5b.1
    have h5d : f z = y := h5b.2
    have h5e : f z = f x := by rwa [←h4] at h5d
    have h5f : z = x := injf h5e
    show x ∈ A j
    rwa [h5f] at h5c
  have h6 : x ∈ ⋂ i, A i := mem_iInter.mpr h5
  have h7 : f x ∈ f '' (⋂ i, A i) := mem_image_of_mem f h6
  show y ∈ f '' (⋂ i, A i)
  rwa [h4] at h7

-- 2ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intros y hy
  -- y : β
  -- hy : y ∈ ⋂ (i : I), f '' A i
  -- ⊢ y ∈ f '' ⋂ (i : I), A i
  rw [mem_iInter] at hy
  -- hy : ∀ (i : I), y ∈ f '' A i
  rcases hy i with ⟨x, -, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ ⋂ (i : I), A i ∧ f x = y
  constructor
  . -- ⊢ x ∈ ⋂ (i : I), A i
    apply mem_iInter_of_mem
    -- ⊢ ∀ (i : I), x ∈ A i
    intro j
    -- j : I
    -- ⊢ x ∈ A j
    rcases hy j with ⟨z, zAj, fzy⟩
    -- z : α
    -- zAj : z ∈ A j
    -- fzy : f z = y
    convert zAj
    -- ⊢ x = z
    apply injf
    -- ⊢ f x = f z
    rw [fxy]
    -- ⊢ y = f z
    rw [←fzy]
  . -- ⊢ f x = y
    exact fxy

-- 3ª demostración
-- ===============

example
  (i : I)
  (injf : Injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
by
  intro y
  -- y : β
  -- ⊢ y ∈ ⋂ (i : I), f '' A i → y ∈ f '' ⋂ (i : I), A i
  simp
  -- ⊢ (∀ (i : I), ∃ x, x ∈ A i ∧ f x = y) → ∃ x, (∀ (i : I), x ∈ A i) ∧ f x = y
  intro h
  -- h : ∀ (i : I), ∃ x, x ∈ A i ∧ f x = y
  -- ⊢ ∃ x, (∀ (i : I), x ∈ A i) ∧ f x = y
  rcases h i with ⟨x, -, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ (∀ (i : I), x ∈ A i) ∧ f x = y
  constructor
  . -- ⊢ ∀ (i : I), x ∈ A i
    intro j
    -- j : I
    -- ⊢ x ∈ A j
    rcases h j with ⟨z, zAi, fzy⟩
    -- z : α
    -- zAi : z ∈ A j
    -- fzy : f z = y
    have : f x = f z := by rw [fxy, fzy]
    -- this : f x = f z
    have : x = z := injf this
    -- this : x = z
    rw [this]
    -- ⊢ z ∈ A j
    exact zAi
  . -- ⊢ f x = y
    exact fxy

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set α)
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_iInter_of_mem : (∀ i, x ∈ A i) → x ∈ ⋂ i, A i)
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_la_interseccion_general_mediante_inyectiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_la_interseccion_general_mediante_inyectiva
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "i ∈ I"
          "inj f"
  shows "(⋂ i ∈ I. f ` A i) ⊆ f ` (⋂ i ∈ I. A i)"
proof (rule subsetI)
  fix y
  assume "y ∈ (⋂ i ∈ I. f ` A i)"
  then have "y ∈ f ` A i"
    using ‹i ∈ I› by (rule INT_D)
  then show "y ∈ f ` (⋂ i ∈ I. A i)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ A i"
    have "x ∈ (⋂ i ∈ I. A i)"
    proof (rule INT_I)
      fix j
      assume "j ∈ I"
      show "x ∈ A j"
      proof -
        have "y ∈ f ` A j"
          using ‹y ∈ (⋂i∈I. f ` A i)› ‹j ∈ I› by (rule INT_D)
        then show "x ∈ A j"
        proof (rule imageE)
          fix z
          assume "y = f z"
          assume "z ∈ A j"
          have "f z = f x"
            using ‹y = f z› ‹y = f x› by (rule subst)
          with ‹inj f› have "z = x"
            by (rule injD)
          then show "x ∈ A j"
            using ‹z ∈ A j› by (rule subst)
        qed
      qed
    qed
    then have "f x ∈ f ` (⋂ i ∈ I. A i)"
      by (rule imageI)
    with ‹y = f x› show "y ∈ f ` (⋂ i ∈ I. A i)"
      by (rule ssubst)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "i ∈ I"
          "inj f"
  shows "(⋂ i ∈ I. f ` A i) ⊆ f ` (⋂ i ∈ I. A i)"
proof
  fix y
  assume "y ∈ (⋂ i ∈ I. f ` A i)"
  then have "y ∈ f ` A i" using ‹i ∈ I› by simp
  then show "y ∈ f ` (⋂ i ∈ I. A i)"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ A i"
    have "x ∈ (⋂ i ∈ I. A i)"
    proof
      fix j
      assume "j ∈ I"
      show "x ∈ A j"
      proof -
        have "y ∈ f ` A j"
          using ‹y ∈ (⋂i∈I. f ` A i)› ‹j ∈ I› by simp
        then show "x ∈ A j"
        proof
          fix z
          assume "y = f z"
          assume "z ∈ A j"
          have "f z = f x" using ‹y = f z› ‹y = f x› by simp
          with ‹inj f› have "z = x" by (rule injD)
          then show "x ∈ A j" using ‹z ∈ A j› by simp
        qed
      qed
    qed
    then have "f x ∈ f ` (⋂ i ∈ I. A i)" by simp
    with ‹y = f x› show "y ∈ f ` (⋂ i ∈ I. A i)" by simp
  qed
qed

(* 3ª demostración *)

lemma
  assumes "i ∈ I"
          "inj f"
  shows "(⋂ i ∈ I. f ` A i) ⊆ f ` (⋂ i ∈ I. A i)"
  using assms
  by (simp add: image_INT)

end
</pre>
