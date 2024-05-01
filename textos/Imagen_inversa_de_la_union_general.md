---
title: Imagen inversa de la unión general
date: 2024-04-30 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 que
\\[ f⁻¹\\left[⋃ᵢ Bᵢ\\right] = ⋃ᵢ f⁻¹[Bᵢ] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α β I : Type _}
variable (f : α → β)
variable (B : I → Set β)

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que, para todo \\(x\\),
\\[ x ∈ f⁻¹\\left[⋃ᵢ Bᵢ\\right] ↔ x ∈ ⋃ᵢ f⁻¹[Bᵢ] \\]
y lo haremos demostrando las dos implicaciones.

(⟹) Supongamos que \\(x ∈ f⁻¹\\left[⋃ᵢ Bᵢ\\right]\\). Entonces, por la definición de la imagen inversa,
\\[ f(x) ∈ ⋃ᵢ Bᵢ \\]
y, por la definición de la unión, existe un \\(i\\) tal que
\\[ f(x) ∈ Bᵢ \\]
y, por la definición de la imagen inversa,
\\[ x ∈ f⁻¹[Bᵢ] \\]
y, por la definición de la unión,
\\[ x ∈ ⋃ᵢ f⁻¹[Bᵢ] \\]

(⟸) Supongamos que \\(x ∈ ⋃ᵢ f⁻¹[Bᵢ]\\). Entonces, por la definición de la unión, existe un \\(i\\) tal que
\\[ x ∈ f⁻¹[Bᵢ] \\]
y, por la definición de la imagen inversa,
\\[ f(x) ∈ Bᵢ \\]
y, por la definición de la unión,
\\[ f(x) ∈ ⋃ᵢ Bᵢ \\]
y, por la definición de la imagen inversa,
\\[ x ∈ f⁻¹\\left[⋃ᵢ Bᵢ\\right] \\]

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

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i ↔ x ∈ ⋃ (i : I), f ⁻¹' B i
  constructor
  . -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i → x ∈ ⋃ (i : I), f ⁻¹' B i
    intro hx
    -- hx : x ∈ f ⁻¹' ⋃ (i : I), B i
    -- ⊢ x ∈ ⋃ (i : I), f ⁻¹' B i
    rw [mem_preimage] at hx
    -- hx : f x ∈ ⋃ (i : I), B i
    rw [mem_iUnion] at hx
    -- hx : ∃ i, f x ∈ B i
    cases' hx with i fxBi
    -- i : I
    -- fxBi : f x ∈ B i
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ f ⁻¹' B i
    use i
    -- ⊢ x ∈ f ⁻¹' B i
    apply mem_preimage.mpr
    -- ⊢ f x ∈ B i
    exact fxBi
  . -- ⊢ x ∈ ⋃ (i : I), f ⁻¹' B i → x ∈ f ⁻¹' ⋃ (i : I), B i
    intro hx
    -- hx : x ∈ ⋃ (i : I), f ⁻¹' B i
    -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i
    rw [mem_preimage]
    -- ⊢ f x ∈ ⋃ (i : I), B i
    rw [mem_iUnion]
    -- ⊢ ∃ i, f x ∈ B i
    rw [mem_iUnion] at hx
    -- hx : ∃ i, x ∈ f ⁻¹' B i
    cases' hx with i xBi
    -- i : I
    -- xBi : x ∈ f ⁻¹' B i
    use i
    -- ⊢ f x ∈ B i
    rw [mem_preimage] at xBi
    -- xBi : f x ∈ B i
    exact xBi

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
preimage_iUnion

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by  simp

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set β)
-- variable (A : I → Set α)
-- #check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
-- #check (mem_preimage : x ∈ f ⁻¹' s ↔ f x ∈ s)
-- #check (preimage_iUnion : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_inversa_de_la_union_general.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_inversa_de_la_union_general
imports Main
begin

(* 1ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
proof (rule equalityI)
  show "f -` (⋃ i ∈ I. B i) ⊆ (⋃ i ∈ I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (⋃ i ∈ I. B i)"
    then have "f x ∈ (⋃ i ∈ I. B i)"
      by (rule vimageD)
    then show "x ∈ (⋃ i ∈ I. f -` B i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "f x ∈ B i"
      then have "x ∈ f -` B i"
        by (rule vimageI2)
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. f -` B i)"
        by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. f -` B i) ⊆ f -` (⋃ i ∈ I. B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (⋃ i ∈ I. f -` B i)"
    then show "x ∈ f -` (⋃ i ∈ I. B i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "x ∈ f -` B i"
      then have "f x ∈ B i"
        by (rule vimageD)
      with ‹i ∈ I› have "f x ∈ (⋃ i ∈ I. B i)"
        by (rule UN_I)
      then show "x ∈ f -` (⋃ i ∈ I. B i)"
        by (rule vimageI2)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
proof
  show "f -` (⋃ i ∈ I. B i) ⊆ (⋃ i ∈ I. f -` B i)"
  proof
    fix x
    assume "x ∈ f -` (⋃ i ∈ I. B i)"
    then have "f x ∈ (⋃ i ∈ I. B i)" by simp
    then show "x ∈ (⋃ i ∈ I. f -` B i)"
    proof
      fix i
      assume "i ∈ I"
      assume "f x ∈ B i"
      then have "x ∈ f -` B i" by simp
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. f -` B i)" by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. f -` B i) ⊆ f -` (⋃ i ∈ I. B i)"
  proof
    fix x
    assume "x ∈ (⋃ i ∈ I. f -` B i)"
    then show "x ∈ f -` (⋃ i ∈ I. B i)"
    proof
      fix i
      assume "i ∈ I"
      assume "x ∈ f -` B i"
      then have "f x ∈ B i" by simp
      with ‹i ∈ I› have "f x ∈ (⋃ i ∈ I. B i)" by (rule UN_I)
      then show "x ∈ f -` (⋃ i ∈ I. B i)" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
  by (simp only: vimage_UN)

(* 4ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
  by auto

end
</pre>
