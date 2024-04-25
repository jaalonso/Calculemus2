---
title: Unión con la imagen inversa
date: 2024-04-24 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
description: Demostraciones con Lean4 e Isabelle/HOL de \"s ∪ f⁻¹[v] ⊆ f⁻¹[f[s] ∪ v]\".
previewimage: "/favicon.png"
---

[mathjax]

Demostrar con Lean4 que
\\[ s ∪ f⁻¹[v] ⊆ f⁻¹[f[s] ∪ v] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ s ∪ f⁻¹[v]\\). Entonces, se pueden dar dos casos.

Caso 1: Supongamos que \\(x ∈ s\\). Entonces, se tiene
\\begin{align}
   &f(x) ∈ f[s]       \\\\
   &f(x) ∈ f[s] ∪ v   \\\\
   &x ∈ f⁻¹[f[s] ∪ v]
\\end{align}

Caso 2: Supongamos que x ∈ f⁻¹[v]. Entonces, se tiene
\\begin{align}
   &f(x) ∈ v           \\\\
   &f(x) ∈ f[s] ∪ v    \\\\
   &x ∈ f⁻¹[f[s] ∪ v]
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

-- 1ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  cases' hx with xs xv
  . -- xs : x ∈ s
    have h1 : f x ∈ f '' s := mem_image_of_mem f xs
    have h2 : f x ∈ f '' s ∪ v := mem_union_left v h1
    show x ∈ f ⁻¹' (f '' s ∪ v)
    exact mem_preimage.mpr h2
  . -- xv : x ∈ f ⁻¹' v
    have h3 : f x ∈ v := mem_preimage.mp xv
    have h4 : f x ∈ f '' s ∪ v := mem_union_right (f '' s) h3
    show x ∈ f ⁻¹' (f '' s ∪ v)
    exact mem_preimage.mpr h4

-- 2ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  rw [mem_preimage]
  -- ⊢ f x ∈ f '' s ∪ v
  cases' hx with xs xv
  . -- xs : x ∈ s
    apply mem_union_left
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- xv : x ∈ f ⁻¹' v
    apply mem_union_right
    -- ⊢ f x ∈ v
    rw [←mem_preimage]
    -- ⊢ x ∈ f ⁻¹' v
    exact xv

-- 3ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  cases' hx with xs xv
  . -- xs : x ∈ s
    rw [mem_preimage]
    -- ⊢ f x ∈ f '' s ∪ v
    apply mem_union_left
    -- ⊢ f x ∈ f '' s
    apply mem_image_of_mem
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
    rw [mem_preimage]
    -- ⊢ f x ∈ f '' s ∪ v
    apply mem_union_right
    -- ⊢ f x ∈ v
    exact xv

-- 4ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  rintro x (xs | xv)
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  . -- xs : x ∈ s
    left
    -- ⊢ f x ∈ f '' s
    exact mem_image_of_mem f xs
  . -- xv : x ∈ f ⁻¹' v
    right
    -- ⊢ f x ∈ v
    exact xv

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  rintro x (xs | xv)
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  . -- xs : x ∈ s
    exact Or.inl (mem_image_of_mem f xs)
  . -- xv : x ∈ f ⁻¹' v
    exact Or.inr xv

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
by
  intros x h
  -- x : α
  -- h : x ∈ s ∪ f ⁻¹' v
  -- ⊢ x ∈ f ⁻¹' (f '' s ∪ v)
  exact Or.elim h (fun xs ↦ Or.inl (mem_image_of_mem f xs)) Or.inr

-- 6ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
fun _ h ↦ Or.elim h (fun xs ↦ Or.inl (mem_image_of_mem f xs)) Or.inr

-- 7ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
union_preimage_subset s v f

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set α)
-- variable (a b c : Prop)
-- #check (Or.elim : a ∨ b → (a → c) → (b → c) → c)
-- #check (Or.inl : a → a ∨ b)
-- #check (Or.inr : b → a ∨ b)
-- #check (mem_image_of_mem f : x  ∈ s → f x ∈ f '' s)
-- #check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
-- #check (mem_union_left t : x ∈ s → x ∈ s ∪ t)
-- #check (mem_union_right s : x ∈ t → x ∈ s ∪ t)
-- #check (union_preimage_subset s v f : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Union_con_la_imagen_inversa.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Union_con_la_imagen_inversa
imports Main
begin

(* 1ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
proof (rule subsetI)
  fix x
  assume "x ∈ s ∪ f -` v"
  then have "f x ∈ f ` s ∪ v"
  proof (rule UnE)
    assume "x ∈ s"
    then have "f x ∈ f ` s"
      by (rule imageI)
    then show "f x ∈ f ` s ∪ v"
      by (rule UnI1)
  next
    assume "x ∈ f -` v"
    then have "f x ∈ v"
      by (rule vimageD)
    then show "f x ∈ f ` s ∪ v"
      by (rule UnI2)
  qed
  then show "x ∈ f -` (f ` s ∪ v)"
    by (rule vimageI2)
qed

(* 2ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
proof
  fix x
  assume "x ∈ s ∪ f -` v"
  then have "f x ∈ f ` s ∪ v"
  proof
    assume "x ∈ s"
    then have "f x ∈ f ` s" by simp
    then show "f x ∈ f ` s ∪ v" by simp
  next
    assume "x ∈ f -` v"
    then have "f x ∈ v" by simp
    then show "f x ∈ f ` s ∪ v" by simp
  qed
  then show "x ∈ f -` (f ` s ∪ v)" by simp
qed

(* 3ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
proof
  fix x
  assume "x ∈ s ∪ f -` v"
  then have "f x ∈ f ` s ∪ v"
  proof
    assume "x ∈ s"
    then show "f x ∈ f ` s ∪ v" by simp
  next
    assume "x ∈ f -` v"
    then show "f x ∈ f ` s ∪ v" by simp
  qed
  then show "x ∈ f -` (f ` s ∪ v)" by simp
qed

(* 4ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
  by auto

end
</pre>
