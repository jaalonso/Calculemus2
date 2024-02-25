---
Título: s ∩ (s ∪ t) = s
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ s ∩ (s ∪ t) = s \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set
variable {α : Type}
variable (s t : Set α)

example : s ∩ (s ∪ t) = s :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que
\\[ (∀ x)[x ∈ s ∩ (s ∪ t) ↔ x ∈ s] \\]
y lo haremos demostrando las dos implicaciones.

(⟹) Sea \\(x ∈ s ∩ (s ∪ t)\\). Entonces, \\(x ∈ s\\).

(⟸) Sea \\(x ∈ s\\). Entonces, \\(x ∈ s ∪ t\\) y, por tanto, \\(x ∈ s ∩ (s ∪ t)\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    intros h
  -- h : x ∈ s ∩ (s ∪ t)
  -- ⊢ x ∈ s
    exact h.1
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    intro h
    -- h : x ∈ s ∩ (s ∪ t)
    -- ⊢ x ∈ s
    exact h.1
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ s ∪ t
      exact (Or.inl xs)

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  exact ⟨fun h ↦ h.1,
         fun xs ↦ ⟨xs, Or.inl xs⟩⟩

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  exact ⟨And.left,
         fun xs ↦ ⟨xs, Or.inl xs⟩⟩

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∩ (s ∪ t) → x ∈ s
    rintro ⟨xs, -⟩
    -- xs : x ∈ s
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ s → x ∈ s ∩ (s ∪ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    use xs
    -- ⊢ x ∈ s ∪ t
    left
    -- ⊢ x ∈ s
    exact xs

-- 6ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by
  apply subset_antisymm
  . -- ⊢ s ∩ (s ∪ t) ⊆ s
    rintro x ⟨hxs, -⟩
    -- x : α
    -- hxs : x ∈ s
    -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ s ⊆ s ∩ (s ∪ t)
    intros x hxs
    -- x : α
    -- hxs : x ∈ s
    -- ⊢ x ∈ s ∩ (s ∪ t)
    exact ⟨hxs, Or.inl hxs⟩

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self

-- 8ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
by aesop

-- Lemas usados
-- ============

-- variable (a b : Prop)
-- #check (And.left : a ∧ b → a)
-- #check (Or.inl : a → a ∨ b)
-- #check (inf_sup_self : s ∩ (s ∪ t) = s)
-- #check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Interseccion_con_su_union.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Interseccion_con_su_union
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ (s ∪ t) = s"
proof (rule  equalityI)
  show "s ∩ (s ∪ t) ⊆ s"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∩ (s ∪ t)"
    then show "x ∈ s"
      by (simp only: IntD1)
  qed
next
  show "s ⊆ s ∩ (s ∪ t)"
  proof (rule subsetI)
    fix x
    assume "x ∈ s"
    then have "x ∈ s ∪ t"
      by (simp only: UnI1)
    with ‹x ∈ s› show "x ∈ s ∩ (s ∪ t)"
      by (rule IntI)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ (s ∪ t) = s"
proof
  show "s ∩ (s ∪ t) ⊆ s"
  proof
    fix x
    assume "x ∈ s ∩ (s ∪ t)"
    then show "x ∈ s"
      by simp
  qed
next
  show "s ⊆ s ∩ (s ∪ t)"
  proof
    fix x
    assume "x ∈ s"
    then have "x ∈ s ∪ t"
      by simp
    then show "x ∈ s ∩ (s ∪ t)"
      using ‹x ∈ s› by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ (s ∪ t) = s"
by (fact Un_Int_eq)

(* 4ª demostración *)
lemma "s ∩ (s ∪ t) = s"
by auto
</pre>
