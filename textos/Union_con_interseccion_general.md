---
Título: s ∪ (⋂ᵢ Aᵢ) = ⋂ᵢ (Aᵢ ∪ s)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ s ∪ (⋂_i A_i) = ⋂_i (A_i ∪ s) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set
variable {α : Type}
variable (s : Set α)
variable (A : ℕ → Set α)

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para todo \\(x\\),
\\[ x ∈ s ∪ ⋂_i A_i ↔ x ∈ ⋂_i (A i ∪ s) \\]
Lo haremos mediante la siguiente cadena de equivalencias
\\begin{align}
   x ∈ s ∪ ⋂_i A_i &↔ x ∈ s ∨ x ∈ ⋂_i A_i \\\\
                   &↔ x ∈ s ∨ (∀ i)[x ∈ A_i] \\\\
                   &↔ (∀ i)[x ∈ s ∨ x ∈ A_i] \\\\
                   &↔ (∀ i)[x ∈ A_i ∨ x ∈ s] \\\\
                   &↔ (∀ i)[x ∈ A_i ∪ s]     \\\\
                   &↔ x ∈ ⋂_i (A_i ∪ s)
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s : Set α)
variable (A : ℕ → Set α)

-- 1ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ ⋂ (i : ℕ), A i ↔ x ∈ ⋂ (i : ℕ), A i ∪ s
  calc x ∈ s ∪ ⋂ i, A i
     ↔ x ∈ s ∨ x ∈ ⋂ i, A i :=
         by simp only [mem_union]
   _ ↔ x ∈ s ∨ ∀ i, x ∈ A i :=
         by simp only [mem_iInter]
   _ ↔ ∀ i, x ∈ s ∨ x ∈ A i :=
         by simp only [forall_or_left]
   _ ↔ ∀ i, x ∈ A i ∨ x ∈ s  :=
         by simp only [or_comm]
   _ ↔ ∀ i, x ∈ A i ∪ s  :=
         by simp only [mem_union]
   _ ↔ x ∈ ⋂ i, A i ∪ s :=
         by simp only [mem_iInter]

-- 2ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ ⋂ (i : ℕ), A i ↔ x ∈ ⋂ (i : ℕ), A i ∪ s
  simp only [mem_union, mem_iInter]
  -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) ↔ ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) → ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    intros h i
    -- h : x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    -- i : ℕ
    -- ⊢ x ∈ A i ∨ x ∈ s
    rcases h with (xs | xAi)
    . -- xs : x ∈ s
      right
      -- ⊢ x ∈ s
      exact xs
    . -- xAi : ∀ (i : ℕ), x ∈ A i
      left
      -- ⊢ x ∈ A i
      exact xAi i
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∨ x ∈ s) → x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    -- ⊢ x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    by_cases cxs : x ∈ s
    . -- cxs : x ∈ s
      left
      -- ⊢ x ∈ s
      exact cxs
    . -- cns : ¬x ∈ s
      right
      -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      rcases h i with (xAi | xs)
      . -- ⊢ x ∈ A i
        exact xAi
      . -- xs : x ∈ s
        exact absurd xs cxs

-- 3ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ ⋂ (i : ℕ), A i ↔ x ∈ ⋂ (i : ℕ), A i ∪ s
  simp only [mem_union, mem_iInter]
  -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) ↔ ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∨ ∀ (i : ℕ), x ∈ A i) → ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    rintro (xs | xI) i
    . -- xs : x ∈ s
      -- i : ℕ
      -- ⊢ x ∈ A i ∨ x ∈ s
      right
      -- ⊢ x ∈ s
      exact xs
    . -- xI : ∀ (i : ℕ), x ∈ A i
      -- i : ℕ
      -- ⊢ x ∈ A i ∨ x ∈ s
      left
      -- ⊢ x ∈ A i
      exact xI i
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∨ x ∈ s) → x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∨ x ∈ s
    -- ⊢ x ∈ s ∨ ∀ (i : ℕ), x ∈ A i
    by_cases cxs : x ∈ s
    . -- cxs : x ∈ s
      left
      -- ⊢ x ∈ s
      exact cxs
    . -- cxs : ¬x ∈ s
      right
      -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      cases h i
      . -- h : x ∈ A i
        assumption
      . -- h : x ∈ s
        contradiction

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s t : Set α)
-- variable (a b q : Prop)
-- variable (p : ℕ → Prop)
-- #check (absurd : a → ¬a → b)
-- #check (forall_or_left : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x)
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_union x a b : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
-- #check (or_comm : a ∨ b ↔ b ∨ a)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Union_con_interseccion_general.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Union_con_interseccion_general
imports Main
begin

(* 1ª demostración *)
lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof (rule equalityI)
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof (rule UnE)
      assume "x ∈ s"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof (rule INT_I)
        fix i
        assume "i ∈ I"
        show "x ∈ A i ∪ s"
          using ‹x ∈ s› by (rule UnI2)
      qed
    next
      assume h1 : "x ∈ (⋂ i ∈ I. A i)"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof (rule INT_I)
        fix i
        assume "i ∈ I"
        with h1 have "x ∈ A i"
          by (rule INT_D)
        then show "x ∈ A i ∪ s"
          by (rule UnI1)
      qed
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof (rule subsetI)
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      assume "x ∈ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by (rule UnI1)
    next
      assume "x ∉ s"
      have "x ∈ (⋂ i ∈ I. A i)"
      proof (rule INT_I)
        fix i
        assume "i ∈ I"
        with h2 have "x ∈ A i ∪ s"
          by (rule INT_D)
        then show "x ∈ A i"
        proof (rule UnE)
          assume "x ∈ A i"
          then show "x ∈ A i"
            by this
        next
          assume "x ∈ s"
          with ‹x ∉ s› show "x ∈ A i"
            by (rule notE)
        qed
      qed
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by (rule UnI2)
    qed
  qed
qed

(* 2ª demostración *)
lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof
      assume "x ∈ s"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof
        fix i
        assume "i ∈ I"
        show "x ∈ A i ∪ s"
          using ‹x ∈ s› by simp
      qed
    next
      assume h1 : "x ∈ (⋂ i ∈ I. A i)"
      show "x ∈ (⋂ i ∈ I. A i ∪ s)"
      proof
        fix i
        assume "i ∈ I"
        with h1 have "x ∈ A i"
          by simp
        then show "x ∈ A i ∪ s"
          by simp
      qed
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      assume "x ∈ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by simp
    next
      assume "x ∉ s"
      have "x ∈ (⋂ i ∈ I. A i)"
      proof
        fix i
        assume "i ∈ I"
        with h2 have "x ∈ A i ∪ s"
          by (rule INT_D)
        then show "x ∈ A i"
        proof
          assume "x ∈ A i"
          then show "x ∈ A i"
            by this
        next
          assume "x ∈ s"
          with ‹x ∉ s› show "x ∈ A i"
            by simp
        qed
      qed
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by simp
    qed
  qed
qed

(* 3ª demostración *)
lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof
      assume "x ∈ s"
      then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
        by simp
    next
      assume "x ∈ (⋂ i ∈ I. A i)"
      then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
        by simp
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      assume "x ∈ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        by simp
    next
      assume "x ∉ s"
      then show "x ∈ s ∪ (⋂ i ∈ I. A i)"
        using h2 by simp
    qed
  qed
qed

(* 4ª demostración *)
lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
proof
  show "s ∪ (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. A i ∪ s)"
  proof
    fix x
    assume "x ∈ s ∪ (⋂ i ∈ I. A i)"
    then show "x ∈ (⋂ i ∈ I. A i ∪ s)"
    proof
      assume "x ∈ s"
      then show ?thesis by simp
    next
      assume "x ∈ (⋂ i ∈ I. A i)"
      then show ?thesis by simp
    qed
  qed
next
  show "(⋂ i ∈ I. A i ∪ s) ⊆ s ∪ (⋂ i ∈ I. A i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i ∪ s)"
    show "x ∈ s ∪ (⋂ i ∈ I. A i)"
    proof (cases "x ∈ s")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis using h2 by simp
    qed
  qed
qed

(* 5ª demostración *)
lemma "s ∪ (⋂ i ∈ I. A i) = (⋂ i ∈ I. A i ∪ s)"
  by auto

end
</pre>
