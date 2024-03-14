---
Título: f[s ∪ t] = f[s] ∪ f[t]
Autor:  José A. Alonso
---

[mathjax]

En Lean4, la imagen de un conjunto s por una función f se representa por `f '' s`; es decir,
<pre lang="lean">
   f '' s = {y | ∃ x, x ∈ s ∧ f x = y}
</pre>

Demostrar con Lean4 que
<pre lang="lean">
   f '' (s ∪ t) = f '' s ∪ f '' t
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)
open Set

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar, para todo \\(y\\), que
\\[ y ∈ f[s ∪ t] ↔ y ∈ f[s] ∪ f[t] \\]
Lo haremos mediante la siguiente cadena de equivalencias
\\begin{align}
   y ∈ f[s ∪ t] &↔ (∃x)(x ∈ s ∪ t ∧ f x = y) \\\\
                &↔ (∃x)((x ∈ s ∨ x ∈ t) ∧ f x = y) \\\\
                &↔ (∃x)((x ∈ s ∧ f x = y) ∨ (x ∈ t ∧ f x = y)) \\\\
                &↔ (∃x)(x ∈ s ∧ f x = y) ∨ (∃x)(x ∈ t ∧ f x = y) \\\\
                &↔ y ∈ f[s] ∨ y ∈ f[t] \\\\
                &↔ y ∈ f[s] ∪ f[t]
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)

open Set

-- 1ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  calc y ∈ f '' (s ∪ t)
     ↔ ∃ x, x ∈ s ∪ t ∧ f x = y :=
         by simp only [mem_image]
   _ ↔ ∃ x, (x ∈ s ∨ x ∈ t) ∧ f x = y :=
         by simp only [mem_union]
   _ ↔ ∃ x, (x ∈ s ∧ f x = y) ∨ (x ∈ t ∧ f x = y) :=
         by simp only [or_and_right]
   _ ↔ (∃ x, x ∈ s ∧ f x = y) ∨ (∃ x, x ∈ t ∧ f x = y) :=
         by simp only [exists_or]
   _ ↔ y ∈ f '' s ∨ y ∈ f '' t :=
         by simp only [mem_image]
   _ ↔ y ∈ f '' s ∪ f '' t :=
         by simp only [mem_union]

-- 2ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  constructor
  . -- ⊢ y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
    intro h
    -- h : y ∈ f '' (s ∪ t)
    -- ⊢ y ∈ f '' s ∪ f '' t
    rw [mem_image] at h
    -- h : ∃ x, x ∈ s ∪ t ∧ f x = y
    rcases h with ⟨x, hx⟩
    -- x : α
    -- hx : x ∈ s ∪ t ∧ f x = y
    rcases hx with ⟨xst, fxy⟩
    -- xst : x ∈ s ∪ t
    -- fxy : f x = y
    rw [←fxy]
    -- ⊢ f x ∈ f '' s ∪ f '' t
    rw [mem_union] at xst
    -- xst : x ∈ s ∨ x ∈ t
    rcases xst with (xs | xt)
    . -- xs : x ∈ s
      apply mem_union_left
      -- ⊢ f x ∈ f '' s
      apply mem_image_of_mem
      -- ⊢ x ∈ s
      exact xs
    . -- xt : x ∈ t
      apply mem_union_right
      -- ⊢ f x ∈ f '' t
      apply mem_image_of_mem
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t)
    intro h
    -- h : y ∈ f '' s ∪ f '' t
    -- ⊢ y ∈ f '' (s ∪ t)
    rw [mem_union] at h
    -- h : y ∈ f '' s ∨ y ∈ f '' t
    rcases h with (yfs | yft)
    . -- yfs : y ∈ f '' s
      rw [mem_image]
      -- ⊢ ∃ x, x ∈ s ∪ t ∧ f x = y
      rw [mem_image] at yfs
      -- yfs : ∃ x, x ∈ s ∧ f x = y
      rcases yfs with ⟨x, hx⟩
      -- x : α
      -- hx : x ∈ s ∧ f x = y
      rcases hx with ⟨xs, fxy⟩
      -- xs : x ∈ s
      -- fxy : f x = y
      use x
      -- ⊢ x ∈ s ∪ t ∧ f x = y
      constructor
      . -- ⊢ x ∈ s ∪ t
        apply mem_union_left
        -- ⊢ x ∈ s
        exact xs
      . -- ⊢ f x = y
        exact fxy
    . -- yft : y ∈ f '' t
      rw [mem_image]
      -- ⊢ ∃ x, x ∈ s ∪ t ∧ f x = y
      rw [mem_image] at yft
      -- yft : ∃ x, x ∈ t ∧ f x = y
      rcases yft with ⟨x, hx⟩
      -- x : α
      -- hx : x ∈ t ∧ f x = y
      rcases hx with ⟨xt, fxy⟩
      -- xt : x ∈ t
      -- fxy : f x = y
      use x
      -- ⊢ x ∈ s ∪ t ∧ f x = y
      constructor
      . -- ⊢ x ∈ s ∪ t
        apply mem_union_right
        -- ⊢ x ∈ t
        exact xt
      . -- ⊢ f x = y
        exact fxy

-- 3ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  constructor
  . -- ⊢ y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
    rintro ⟨x, xst, rfl⟩
    -- x : α
    -- xst : x ∈ s ∪ t
    -- ⊢ f x ∈ f '' s ∪ f '' t
    rcases xst with (xs | xt)
    . -- xs : x ∈ s
      left
      -- ⊢ f x ∈ f '' s
      exact mem_image_of_mem f xs
    . -- xt : x ∈ t
      right
      -- ⊢ f x ∈ f '' t
      exact mem_image_of_mem f xt
  . -- ⊢ y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t)
    rintro (yfs | yft)
    . -- yfs : y ∈ f '' s
      rcases yfs with ⟨x, xs, rfl⟩
      -- x : α
      -- xs : x ∈ s
      -- ⊢ f x ∈ f '' (s ∪ t)
      apply mem_image_of_mem
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs
    . -- yft : y ∈ f '' t
      rcases yft with ⟨x, xt, rfl⟩
      -- x : α
      -- xs : x ∈ s
      -- ⊢ f x ∈ f '' (s ∪ t)
      apply mem_image_of_mem
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt

-- 4ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  constructor
  . -- ⊢ y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
    rintro ⟨x, xst, rfl⟩
    -- x : α
    -- xst : x ∈ s ∪ t
    -- ⊢ f x ∈ f '' s ∪ f '' t
    rcases xst with (xs | xt)
    . -- xs : x ∈ s
      left
      -- ⊢ f x ∈ f '' s
      use x, xs
    . -- xt : x ∈ t
      right
      -- ⊢ f x ∈ f '' t
      use x, xt
  . rintro (yfs | yft)
    . -- yfs : y ∈ f '' s
      rcases yfs with ⟨x, xs, rfl⟩
      -- x : α
      -- xs : x ∈ s
      -- ⊢ f x ∈ f '' (s ∪ t)
      use x, Or.inl xs
    . -- yft : y ∈ f '' t
      rcases yft with ⟨x, xt, rfl⟩
      -- x : α
      -- xt : x ∈ t
      -- ⊢ f x ∈ f '' (s ∪ t)
      use x, Or.inr xt

-- 5ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  constructor
  . -- ⊢ y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
    rintro ⟨x, xs | xt, rfl⟩
    . -- x : α
      -- xs : x ∈ s
      -- ⊢ f x ∈ f '' s ∪ f '' t
      left
      -- ⊢ f x ∈ f '' s
      use x, xs
    . -- x : α
      -- xt : x ∈ t
      -- ⊢ f x ∈ f '' s ∪ f '' t
      right
      -- ⊢ f x ∈ f '' t
      use x, xt
  . -- ⊢ y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t)
    rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
    . -- x : α
      -- xs : x ∈ s
      -- ⊢ f x ∈ f '' (s ∪ t)
      use x, Or.inl xs
    . -- x : α
      -- xt : x ∈ t
      -- ⊢ f x ∈ f '' (s ∪ t)
      use x, Or.inr xt

-- 6ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  constructor
  . -- ⊢ y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
    aesop
  . -- ⊢ y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t)
    aesop

-- 7ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  constructor <;> aesop

-- 8ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  rw [iff_def]
  -- ⊢ (y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t) ∧ (y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t))
  aesop

-- 9ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
image_union f s t

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (y : β)
-- variable (a b c : Prop)
-- variable (p q : α → Prop)
-- #check (Or.inl : a → a ∨ b)
-- #check (Or.inr : b → a ∨ b)
-- #check (exists_or : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ ∃ x, q x)
-- #check (iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a))
-- #check (image_union f s t : f '' (s ∪ t) = f '' s ∪ f '' t)
-- #check (mem_image f s y : (y ∈ f '' s ↔ ∃ (x : α), x ∈ s ∧ f x = y))
-- #check (mem_image_of_mem  f : x ∈ s → f x ∈ f '' s)
-- #check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
-- #check (mem_union_left t : x ∈ s → x ∈ s ∪ t)
-- #check (mem_union_right s : x ∈ t → x ∈ s ∪ t)
-- #check (or_and_right : (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_de_la_union.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_de_la_union
imports Main
begin

(* 1ª demostración *)
lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
proof (rule equalityI)
  show "f ` (s ∪ t) ⊆ f ` s ∪ f ` t"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` (s ∪ t)"
    then show "y ∈ f ` s ∪ f ` t"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x ∈ s ∪ t"
      then show "y ∈ f ` s ∪ f ` t"
      proof (rule UnE)
        assume "x ∈ s"
        with ‹y = f x› have "y ∈ f ` s"
          by (simp only: image_eqI)
        then show "y ∈ f ` s ∪ f ` t"
          by (rule UnI1)
      next
        assume "x ∈ t"
        with ‹y = f x› have "y ∈ f ` t"
          by (simp only: image_eqI)
        then show "y ∈ f ` s ∪ f ` t"
          by (rule UnI2)
      qed
    qed
  qed
next
  show "f ` s ∪ f ` t ⊆ f ` (s ∪ t)"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` s ∪ f ` t"
    then show "y ∈ f ` (s ∪ t)"
    proof (rule UnE)
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∪ t)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x ∈ s"
        then have "x ∈ s ∪ t"
          by (rule UnI1)
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by (simp only: image_eqI)
      qed
    next
      assume "y ∈ f ` t"
      then show "y ∈ f ` (s ∪ t)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x ∈ t"
        then have "x ∈ s ∪ t"
          by (rule UnI2)
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by (simp only: image_eqI)
      qed
    qed
  qed
qed

(* 2ª demostración *)
lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
proof
  show "f ` (s ∪ t) ⊆ f ` s ∪ f ` t"
  proof
    fix y
    assume "y ∈ f ` (s ∪ t)"
    then show "y ∈ f ` s ∪ f ` t"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s ∪ t"
      then show "y ∈ f ` s ∪ f ` t"
      proof
        assume "x ∈ s"
        with ‹y = f x› have "y ∈ f ` s"
          by simp
        then show "y ∈ f ` s ∪ f ` t"
          by simp
      next
        assume "x ∈ t"
        with ‹y = f x› have "y ∈ f ` t"
          by simp
        then show "y ∈ f ` s ∪ f ` t"
          by simp
      qed
    qed
  qed
next
  show "f ` s ∪ f ` t ⊆ f ` (s ∪ t)"
  proof
    fix y
    assume "y ∈ f ` s ∪ f ` t"
    then show "y ∈ f ` (s ∪ t)"
    proof
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∪ t)"
      proof
        fix x
        assume "y = f x"
        assume "x ∈ s"
        then have "x ∈ s ∪ t"
          by simp
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by simp
      qed
    next
      assume "y ∈ f ` t"
      then show "y ∈ f ` (s ∪ t)"
      proof
        fix x
        assume "y = f x"
        assume "x ∈ t"
        then have "x ∈ s ∪ t"
          by simp
        with ‹y = f x› show "y ∈ f ` (s ∪ t)"
          by simp
      qed
    qed
  qed
qed

(* 3ª demostración *)
lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
  by (simp only: image_Un)

(* 4ª demostración *)
lemma "f ` (s ∪ t) = f ` s ∪ f ` t"
  by auto

end
</pre>
