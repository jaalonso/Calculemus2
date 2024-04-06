---
Título: f⁻¹[A ∪ B] = f⁻¹[A] ∪ f⁻¹[B].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que \\(f⁻¹[A ∪ B] = f⁻¹[A] ∪ f⁻¹[B]\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (A B : Set β)

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que, para todo \\(x\\),
\\[ x ∈ f⁻¹[A ∪ B] ↔ x ∈ f⁻¹[A] ∪ f⁻¹[B] \\]
Lo haremos demostrando las dos implicaciones.

(⟹) Supongamos que \\(x ∈ f⁻¹[A ∪ B]\\). Entonces, \\(f(x) ∈ A ∪ B\\).
Distinguimos dos casos:

Caso 1: Supongamos que \\(f(x) ∈ A\\). Entonces, \\(x ∈ f⁻¹[A]\\) y, por tanto,
\\(x ∈ f⁻¹[A] ∪ f⁻¹[B]\\).

Caso 2: Supongamos que \\(f(x) ∈ B\\). Entonces, \\(x ∈ f⁻¹[B]\\) y, por tanto,
\\(x ∈ f⁻¹[A] ∪ f⁻¹[B]\\).

(⟸) Supongamos que \\(x ∈ f⁻¹[A] ∪ f⁻¹[B]\\). Distinguimos dos casos.

Caso 1: Supongamos que \\(x ∈ f⁻¹[A]\\). Entonces, \\(f(x) ∈ A\\) y, por tanto,
\\(f(x) ∈ A ∪ B\\). Luego, \\(x ∈ f⁻¹[A ∪ B]\\).

Caso 2: Supongamos que \\(x ∈ f⁻¹[B]\\). Entonces, \\(f(x) ∈ B\\) y, por tanto,
\\(f(x) ∈ A ∪ B\\). Luego, \\(x ∈ f⁻¹[A ∪ B]\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function

open Set

variable {α β : Type _}
variable (f : α → β)
variable (A B : Set β)

-- 1ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    intro h
    -- h : x ∈ f ⁻¹' (A ∪ B)
    -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
    rw [mem_preimage] at h
    -- h : f x ∈ A ∪ B
    rcases h with fxA | fxB
    . -- fxA : f x ∈ A
      left
      -- ⊢ x ∈ f ⁻¹' A
      apply mem_preimage.mpr
      -- ⊢ f x ∈ A
      exact fxA
    . -- fxB : f x ∈ B
      right
      -- ⊢ x ∈ f ⁻¹' B
      apply mem_preimage.mpr
      -- ⊢ f x ∈ B
      exact fxB
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    intro h
    -- h : x ∈ f ⁻¹' A ∪ f ⁻¹' B
    -- ⊢ x ∈ f ⁻¹' (A ∪ B)
    rw [mem_preimage]
    -- ⊢ f x ∈ A ∪ B
    rcases h with xfA | xfB
    . -- xfA : x ∈ f ⁻¹' A
      rw [mem_preimage] at xfA
      -- xfA : f x ∈ A
      left
      -- ⊢ f x ∈ A
      exact xfA
    . -- xfB : x ∈ f ⁻¹' B
      rw [mem_preimage] at xfB
      -- xfB : f x ∈ B
      right
      -- ⊢ f x ∈ B
      exact xfB

-- 2ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    intros h
    -- h : x ∈ f ⁻¹' (A ∪ B)
    -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
    rcases h with fxA | fxB
    . -- fxA : f x ∈ A
      left
      -- ⊢ x ∈ f ⁻¹' A
      exact fxA
    . -- fxB : f x ∈ B
      right
      -- ⊢ x ∈ f ⁻¹' B
      exact fxB
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    intro h
    -- h : x ∈ f ⁻¹' A ∪ f ⁻¹' B
    -- ⊢ x ∈ f ⁻¹' (A ∪ B)
    rcases h with xfA | xfB
    . -- xfA : x ∈ f ⁻¹' A
      left
      -- ⊢ f x ∈ A
      exact xfA
    . -- xfB : x ∈ f ⁻¹' B
      right
      -- ⊢ f x ∈ B
      exact xfB

-- 3ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    rintro (fxA | fxB)
    . -- fxA : f x ∈ A
      -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
      exact Or.inl fxA
    . -- fxB : f x ∈ B
      -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B
      exact Or.inr fxB
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    rintro (xfA | xfB)
    . -- xfA : x ∈ f ⁻¹' A
      -- ⊢ x ∈ f ⁻¹' (A ∪ B)
      exact Or.inl xfA
    . -- xfB : x ∈ f ⁻¹' B
      -- ⊢ x ∈ f ⁻¹' (A ∪ B)
      exact Or.inr xfB

-- 4ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  constructor
  . -- ⊢ x ∈ f ⁻¹' (A ∪ B) → x ∈ f ⁻¹' A ∪ f ⁻¹' B
    aesop
  . -- ⊢ x ∈ f ⁻¹' A ∪ f ⁻¹' B → x ∈ f ⁻¹' (A ∪ B)
    aesop

-- 5ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' (A ∪ B) ↔ x ∈ f ⁻¹' A ∪ f ⁻¹' B
  aesop

-- 6ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by ext ; aesop

-- 7ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by ext ; rfl

-- 8ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
rfl

-- 9ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
preimage_union

-- 10ª demostración
-- ===============

example : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
by simp

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (p q : Prop)
-- #check (Or.inl: p → p ∨ q)
-- #check (Or.inr: q → p ∨ q)
-- #check (mem_preimage : x ∈ f ⁻¹' A ↔ f x ∈ A)
-- #check (preimage_union : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Imagen_inversa_de_la_union.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Imagen_inversa_de_la_union
imports Main
begin

(* 1ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
proof (rule equalityI)
  show "f -` (u ∪ v) ⊆ f -` u ∪ f -` v"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (u ∪ v)"
    then have "f x ∈ u ∪ v"
      by (rule vimageD)
    then show "x ∈ f -` u ∪ f -` v"
    proof (rule UnE)
      assume "f x ∈ u"
      then have "x ∈ f -` u"
        by (rule vimageI2)
      then show "x ∈ f -` u ∪ f -` v"
        by (rule UnI1)
    next
      assume "f x ∈ v"
      then have "x ∈ f -` v"
        by (rule vimageI2)
      then show "x ∈ f -` u ∪ f -` v"
        by (rule UnI2)
    qed
  qed
next
  show "f -` u ∪ f -` v ⊆ f -` (u ∪ v)"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` u ∪ f -` v"
    then show "x ∈ f -` (u ∪ v)"
    proof (rule UnE)
      assume "x ∈ f -` u"
      then have "f x ∈ u"
        by (rule vimageD)
      then have "f x ∈ u ∪ v"
        by (rule UnI1)
      then show "x ∈ f -` (u ∪ v)"
        by (rule vimageI2)
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v"
        by (rule vimageD)
      then have "f x ∈ u ∪ v"
        by (rule UnI2)
      then show "x ∈ f -` (u ∪ v)"
        by (rule vimageI2)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
proof
  show "f -` (u ∪ v) ⊆ f -` u ∪ f -` v"
  proof
    fix x
    assume "x ∈ f -` (u ∪ v)"
    then have "f x ∈ u ∪ v" by simp
    then show "x ∈ f -` u ∪ f -` v"
    proof
      assume "f x ∈ u"
      then have "x ∈ f -` u" by simp
      then show "x ∈ f -` u ∪ f -` v" by simp
    next
      assume "f x ∈ v"
      then have "x ∈ f -` v" by simp
      then show "x ∈ f -` u ∪ f -` v" by simp
    qed
  qed
next
  show "f -` u ∪ f -` v ⊆ f -` (u ∪ v)"
  proof
    fix x
    assume "x ∈ f -` u ∪ f -` v"
    then show "x ∈ f -` (u ∪ v)"
    proof
      assume "x ∈ f -` u"
      then have "f x ∈ u" by simp
      then have "f x ∈ u ∪ v" by simp
      then show "x ∈ f -` (u ∪ v)" by simp
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v" by simp
      then have "f x ∈ u ∪ v" by simp
      then show "x ∈ f -` (u ∪ v)" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
  by (simp only: vimage_Un)

(* 4ª demostración *)

lemma "f -` (u ∪ v) = f -` u ∪ f -` v"
  by auto

end
</pre>
