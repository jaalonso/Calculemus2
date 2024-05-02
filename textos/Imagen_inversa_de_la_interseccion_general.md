---
title: Imagen inversa de la intersección general
date: 2024-05-01 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 que
\\[ f⁻¹\\left[\\bigcap_{i \\in I} B_i\\right] = \\bigcap_{i \\in I} f⁻¹[B_i] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α β I : Type _}
variable (f : α → β)
variable (B : I → Set β)

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se demuestra mediante la siguiente cadena de equivalencias
\\begin{align}
   x ∈ f⁻¹\\left[\\bigcap_{i \\in I} B_i\\right]
   &↔ f(x) ∈ \\bigcap_{i \\in I} B_i            \\\\
   &↔ (∀ i) f(x) ∈ B_i                       \\\\
   &↔ (∀ i) x ∈ f⁻¹[B_i]                     \\\\
   &↔ x ∈ \\bigcap_{i \\in I} f⁻¹[B_i]
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α β I : Type _}
variable (f : α → β)
variable (B : I → Set β)

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  calc  (x ∈ f ⁻¹' ⋂ i, B i)
     ↔ f x ∈ ⋂ i, B i       := mem_preimage
   _ ↔ (∀ i, f x ∈ B i)     := mem_iInter
   _ ↔ (∀ i, x ∈ f ⁻¹' B i) := iff_of_eq rfl
   _ ↔ x ∈ ⋂ i, f ⁻¹' B i   := mem_iInter.symm

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  constructor
  . -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i → x ∈ ⋂ (i : I), f ⁻¹' B i
    intro hx
    -- hx : x ∈ f ⁻¹' ⋂ (i : I), B i
    -- ⊢ x ∈ ⋂ (i : I), f ⁻¹' B i
    apply mem_iInter_of_mem
    -- ⊢ ∀ (i : I), x ∈ f ⁻¹' B i
    intro i
    -- i : I
    -- ⊢ x ∈ f ⁻¹' B i
    rw [mem_preimage]
    -- ⊢ f x ∈ B i
    rw [mem_preimage] at hx
    -- hx : f x ∈ ⋂ (i : I), B i
    rw [mem_iInter] at hx
    -- hx : ∀ (i : I), f x ∈ B i
    exact hx i
  . -- ⊢ x ∈ ⋂ (i : I), f ⁻¹' B i → x ∈ f ⁻¹' ⋂ (i : I), B i
    intro hx
    -- hx : x ∈ ⋂ (i : I), f ⁻¹' B i
    -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i
    rw [mem_preimage]
    -- ⊢ f x ∈ ⋂ (i : I), B i
    rw [mem_iInter]
    -- ⊢ ∀ (i : I), f x ∈ B i
    intro i
    -- i : I
    -- ⊢ f x ∈ B i
    rw [←mem_preimage]
    -- ⊢ x ∈ f ⁻¹' B i
    rw [mem_iInter] at hx
    -- hx : ∀ (i : I), x ∈ f ⁻¹' B i
    exact hx i

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  simp

-- 4ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext ; simp }

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set β)
-- variable (A : I → Set α)
-- variable (a b : Prop)
-- #check (iff_of_eq : a = b → (a ↔ b))
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_iInter_of_mem : (∀ i, x ∈ A i) → x ∈ ⋂ i, A i)
-- #check (mem_preimage : x ∈ f ⁻¹' s ↔ f x ∈ s)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_inversa_de_la_interseccion_general.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_inversa_de_la_interseccion_general
imports Main
begin

(* 1ª demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
proof (rule equalityI)
  show "f -` (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. f -` B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      have "f x ∈ (⋂ i ∈ I. B i)"
        using ‹x ∈ f -` (⋂ i ∈ I. B i)› by (rule vimageD)
      then have "f x ∈ B i"
        using ‹i ∈ I› by (rule INT_D)
      then show "x ∈ f -` B i"
        by (rule vimageI2)
    qed
  qed
next
  show "(⋂ i ∈ I. f -` B i) ⊆ f -` (⋂ i ∈ I. B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (⋂ i ∈ I. f -` B i)"
    have "f x ∈ (⋂ i ∈ I. B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with ‹x ∈ (⋂ i ∈ I. f -` B i)› have "x ∈ f -` B i"
        by (rule INT_D)
      then show "f x ∈ B i"
        by (rule vimageD)
    qed
    then show "x ∈ f -` (⋂ i ∈ I. B i)"
      by (rule vimageI2)
  qed
qed

(* 2ª demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
proof
  show "f -` (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume hx : "x ∈ f -` (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. f -` B i)"
    proof
      fix i
      assume "i ∈ I"
      have "f x ∈ (⋂ i ∈ I. B i)" using hx by simp
      then have "f x ∈ B i" using ‹i ∈ I› by simp
      then show "x ∈ f -` B i" by simp
    qed
  qed
next
  show "(⋂ i ∈ I. f -` B i) ⊆ f -` (⋂ i ∈ I. B i)"
  proof
    fix x
    assume "x ∈ (⋂ i ∈ I. f -` B i)"
    have "f x ∈ (⋂ i ∈ I. B i)"
    proof
      fix i
      assume "i ∈ I"
      with ‹x ∈ (⋂ i ∈ I. f -` B i)› have "x ∈ f -` B i" by simp
      then show "f x ∈ B i" by simp
    qed
    then show "x ∈ f -` (⋂ i ∈ I. B i)" by simp
  qed
qed

(* 3 demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
  by (simp only: vimage_INT)

(* 4ª demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
  by auto

end
</pre>
