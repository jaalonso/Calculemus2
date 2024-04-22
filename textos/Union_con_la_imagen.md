---
title: Unión con la imagen
date: 2024-04-22 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 que
\\[ f[s ∪ f⁻¹[v]] ⊆ f[s] ∪ v \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable (α β : Type _)
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(y ∈ f[s ∪ f⁻¹[v]]\\). Entonces, existe un x tal que
\\begin{align}
   &x ∈ s ∪ f⁻¹[v] \\tag{1} \\\\
   &f(x) = y       \\tag{2}
\\end{align}
De (1), se tiene que \\(x ∈ s\\) ó \\(x ∈ f⁻¹[v]\\). Vamos a demostrar en ambos casos que
\\[ y ∈ f[s] ∪ v \\]

**Caso 1**: Supongamos que \\(x ∈ s\\). Entonces,
\\[ f(x) ∈ f[s] \\]
y, por (2), se tiene que
\\[ y ∈ f[s] \\]
Por tanto,
\\[ y ∈ f[s] ∪ v \\]

**Caso 2**: Supongamos que \\(x ∈ f⁻¹[v]\\). Entonces,
\\[ f(x) ∈ v \\]
y, por (2), se tiene que
\\[ y ∈ v \\]
Por tanto,
\\[ y ∈ f[s] ∪ v \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable (α β : Type _)
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  intros y hy
  obtain ⟨x : α, hx : x ∈ s ∪ f ⁻¹' v ∧ f x = y⟩ := hy
  obtain ⟨hx1 : x ∈ s ∪ f ⁻¹' v, fxy : f x = y⟩ := hx
  cases' hx1 with xs xv
  . -- xs : x ∈ s
    have h1 : f x ∈ f '' s := mem_image_of_mem f xs
    have h2 : y ∈ f '' s := by rwa [fxy] at h1
    show y ∈ f '' s ∪ v
    exact mem_union_left v h2
  . -- xv : x ∈ f ⁻¹' v
    have h3 : f x ∈ v := mem_preimage.mp xv
    have h4 : y ∈ v := by rwa [fxy] at h3
    show y ∈ f '' s ∪ v
    exact mem_union_right (f '' s) h4

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  intros y hy
  obtain ⟨x : α, hx : x ∈ s ∪ f ⁻¹' v ∧ f x = y⟩ := hy
  obtain ⟨hx1 : x ∈ s ∪ f ⁻¹' v, fxy : f x = y⟩ := hx
  cases' hx1 with xs xv
  . -- xs : x ∈ s
    left
    -- ⊢ y ∈ f '' s
    use x
    -- ⊢ x ∈ s ∧ f x = y
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' s ∪ v
    right
    -- ⊢ y ∈ v
    rw [←fxy]
    -- ⊢ f x ∈ v
    exact xv

-- 2ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  rintro y ⟨x, xs | xv, fxy⟩
  -- y : β
  -- x : α
  . -- xs : x ∈ s
    -- ⊢ y ∈ f '' s ∪ v
    left
    -- ⊢ y ∈ f '' s
    use x, xs
    -- ⊢ f x = y
    exact fxy
  . -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∪ v
    right
    -- ⊢ y ∈ v
    rw [←fxy]
    -- ⊢ f x ∈ v
    exact xv

-- 3ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
by
  rintro y ⟨x, xs | xv, fxy⟩ <;>
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set α)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
-- #check (mem_union_left t : x ∈ s → x ∈ s ∪ t)
-- #check (mem_union_right s : x ∈ t → x ∈ s ∪ t)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Union_con_la_imagen.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Union_con_la_imagen
imports Main
begin

(* 1ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v"
    proof (rule UnE)
      assume "x ∈ s"
      then have "f x ∈ f ` s"
        by (rule imageI)
      with ‹y = f x› have "y ∈ f ` s"
        by (rule ssubst)
      then show "y ∈ f ` s ∪ v"
        by (rule UnI1)
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v"
        by (rule vimageD)
      with ‹y = f x› have "y ∈ v"
        by (rule ssubst)
      then show "y ∈ f ` s ∪ v"
        by (rule UnI2)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v"
    proof
      assume "x ∈ s"
      then have "f x ∈ f ` s" by simp
      with ‹y = f x› have "y ∈ f ` s" by simp
      then show "y ∈ f ` s ∪ v" by simp
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v" by simp
      with ‹y = f x› have "y ∈ v" by simp
      then show "y ∈ f ` s ∪ v" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v"
    proof
      assume "x ∈ s"
      then show "y ∈ f ` s ∪ v" by (simp add: ‹y = f x›)
    next
      assume "x ∈ f -` v"
      then show "y ∈ f ` s ∪ v" by (simp add: ‹y = f x›)
    qed
  qed
qed

(* 4ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v" using ‹y = f x› by blast
  qed
qed

(* 5ª demostración *)

lemma "f ` (s ∪ f -` u) ⊆ f ` s ∪ u"
  by auto

end
</pre>
