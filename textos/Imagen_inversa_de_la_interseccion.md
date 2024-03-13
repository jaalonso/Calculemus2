---
Título: f⁻¹[u ∩ v] = f⁻¹[u] ∩ f⁻¹[v]
Autor:  José A. Alonso
---

[mathjax]

En Lean, la imagen inversa de un conjunto `s` (de elementos de tipo `β`) por la función `f` (de tipo `α → β`) es el conjunto `f ⁻¹' s` de elementos `x` (de tipo `α`) tales que `f x ∈ s`.

Demostrar con Lean4 que
<pre lang="lean">
   f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
variable {α β : Type _}
variable (f : α → β)
variable (u v : Set β)
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que, para todo \\(x\\),
\\[ x ∈ f⁻¹[u ∩ v] ↔ x ∈ f⁻¹[u] ∩ f⁻¹[v] \\]
Lo haremos mediante la siguiente cadena de equivalencias
\\begin{align}
   x ∈ f⁻¹[u ∩ v] &↔ f x ∈ u ∩ v \\\\
                  &↔ f x ∈ u ∧ f x ∈ v \\\\
                  &↔ x ∈ f⁻¹[u] ∧ x ∈ f⁻¹[v] \\\\
                  &↔ x ∈ f⁻¹[u] ∩ f⁻¹[v] \\\\
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

variable {α β : Type _}
variable (f : α → β)
variable (u v : Set β)

open Set

-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∩ v) ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v
  calc x ∈ f ⁻¹' (u ∩ v)
     ↔ f x ∈ u ∩ v :=
         by simp only [mem_preimage]
   _ ↔ f x ∈ u ∧ f x ∈ v :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ f ⁻¹' u ∧ x ∈ f ⁻¹' v :=
         by simp only [mem_preimage]
   _ ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v :=
         by simp only [mem_inter_iff]

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∩ v) ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∩ v) → x ∈ f ⁻¹' u ∩ f ⁻¹' v
    intro h
    -- h : x ∈ f ⁻¹' (u ∩ v)
    -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v
    constructor
    . -- ⊢ x ∈ f ⁻¹' u
      apply mem_preimage.mpr
      -- ⊢ f x ∈ u
      rw [mem_preimage] at h
      -- h : f x ∈ u ∩ v
      exact mem_of_mem_inter_left h
    . -- ⊢ x ∈ f ⁻¹' v
      apply mem_preimage.mpr
      -- ⊢ f x ∈ v
      rw [mem_preimage] at h
      -- h : f x ∈ u ∩ v
      exact mem_of_mem_inter_right h
  . -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v → x ∈ f ⁻¹' (u ∩ v)
    intro h
    -- h : x ∈ f ⁻¹' u ∩ f ⁻¹' v
    -- ⊢ x ∈ f ⁻¹' (u ∩ v)
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u ∩ v
    constructor
    . -- ⊢ f x ∈ u
      apply mem_preimage.mp
      -- ⊢ x ∈ f ⁻¹' u
      exact mem_of_mem_inter_left h
    . -- ⊢ f x ∈ v
      apply mem_preimage.mp
      -- ⊢ x ∈ f ⁻¹' v
      exact mem_of_mem_inter_right h

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (u ∩ v) ↔ x ∈ f ⁻¹' u ∩ f ⁻¹' v
  constructor
  . -- ⊢ x ∈ f ⁻¹' (u ∩ v) → x ∈ f ⁻¹' u ∩ f ⁻¹' v
    intro h
    -- h : x ∈ f ⁻¹' (u ∩ v)
    -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v
    constructor
    . -- ⊢ x ∈ f ⁻¹' u
      simp at *
      -- h : f x ∈ u ∧ f x ∈ v
      -- ⊢ f x ∈ u
      exact h.1
    . -- ⊢ x ∈ f ⁻¹' v
      simp at *
      -- h : f x ∈ u ∧ f x ∈ v
      -- ⊢ f x ∈ v
      exact h.2
  . -- ⊢ x ∈ f ⁻¹' u ∩ f ⁻¹' v → x ∈ f ⁻¹' (u ∩ v)
    intro h
    -- h : x ∈ f ⁻¹' u ∩ f ⁻¹' v
    -- ⊢ x ∈ f ⁻¹' (u ∩ v)
    simp at *
    -- h : f x ∈ u ∧ f x ∈ v
    -- ⊢ f x ∈ u ∧ f x ∈ v
    exact h

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by aesop

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
preimage_inter

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
rfl

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s t : Set α)
-- #check (mem_of_mem_inter_left : x ∈ s ∩ t → x ∈ s)
-- #check (mem_of_mem_inter_right : x ∈ s ∩ t → x ∈ t)
-- #check (mem_preimage : x ∈ f ⁻¹' u ↔ f x ∈ u)
-- #check (preimage_inter : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_inversa_de_la_interseccion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_inversa_de_la_interseccion
imports Main
begin

(* 1ª demostración *)
lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
proof (rule equalityI)
  show "f -` (u ∩ v) ⊆ f -` u ∩ f -` v"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (u ∩ v)"
    then have h : "f x ∈ u ∩ v"
      by (simp only: vimage_eq)
    have "x ∈ f -` u"
    proof -
      have "f x ∈ u"
        using h by (rule IntD1)
      then show "x ∈ f -` u"
        by (rule vimageI2)
    qed
    moreover
    have "x ∈ f -` v"
    proof -
      have "f x ∈ v"
        using h by (rule IntD2)
      then show "x ∈ f -` v"
        by (rule vimageI2)
    qed
    ultimately show "x ∈ f -` u ∩ f -` v"
      by (rule IntI)
  qed
next
  show "f -` u ∩ f -` v ⊆ f -` (u ∩ v)"
  proof (rule subsetI)
    fix x
    assume h2 : "x ∈ f -` u ∩ f -` v"
    have "f x ∈ u"
    proof -
      have "x ∈ f -` u"
        using h2 by (rule IntD1)
      then show "f x ∈ u"
        by (rule vimageD)
    qed
    moreover
    have "f x ∈ v"
    proof -
      have "x ∈ f -` v"
        using h2 by (rule IntD2)
      then show "f x ∈ v"
        by (rule vimageD)
    qed
    ultimately have "f x ∈ u ∩ v"
      by (rule IntI)
    then show "x ∈ f -` (u ∩ v)"
      by (rule vimageI2)
  qed
qed

(* 2ª demostración *)
lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
proof
  show "f -` (u ∩ v) ⊆ f -` u ∩ f -` v"
  proof
    fix x
    assume "x ∈ f -` (u ∩ v)"
    then have h : "f x ∈ u ∩ v"
      by simp
    have "x ∈ f -` u"
    proof -
      have "f x ∈ u"
        using h by simp
      then show "x ∈ f -` u"
        by simp
    qed
    moreover
    have "x ∈ f -` v"
    proof -
      have "f x ∈ v"
        using h by simp
      then show "x ∈ f -` v"
        by simp
    qed
    ultimately show "x ∈ f -` u ∩ f -` v"
      by simp
  qed
next
  show "f -` u ∩ f -` v ⊆ f -` (u ∩ v)"
  proof
    fix x
    assume h2 : "x ∈ f -` u ∩ f -` v"
    have "f x ∈ u"
    proof -
      have "x ∈ f -` u"
        using h2 by simp
      then show "f x ∈ u"
        by simp
    qed
    moreover
    have "f x ∈ v"
    proof -
      have "x ∈ f -` v"
        using h2 by simp
      then show "f x ∈ v"
        by simp
    qed
    ultimately have "f x ∈ u ∩ v"
      by simp
    then show "x ∈ f -` (u ∩ v)"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
proof
  show "f -` (u ∩ v) ⊆ f -` u ∩ f -` v"
  proof
    fix x
    assume h1 : "x ∈ f -` (u ∩ v)"
    have "x ∈ f -` u" using h1 by simp
    moreover
    have "x ∈ f -` v" using h1 by simp
    ultimately show "x ∈ f -` u ∩ f -` v" by simp
  qed
next
  show "f -` u ∩ f -` v ⊆ f -` (u ∩ v)"
  proof
    fix x
    assume h2 : "x ∈ f -` u ∩ f -` v"
    have "f x ∈ u" using h2 by simp
    moreover
    have "f x ∈ v" using h2 by simp
    ultimately have "f x ∈ u ∩ v" by simp
    then show "x ∈ f -` (u ∩ v)" by simp
  qed
qed

(* 4ª demostración *)
lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
  by (simp only: vimage_Int)

(* 5ª demostración *)
lemma "f -` (u ∩ v) = f -` u ∩ f -` v"
  by auto

end
</pre>
