---
Título: s ∩ (⋃ᵢ Aᵢ) = ⋃ᵢ (Aᵢ ∩ s)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ s ∩ ⋃_i A_i = ⋃_i (A_i ∩ s) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s : Set α)
variable (A : ℕ → Set α)

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para cada \\(x\\), se verifica que
\\[ x ∈ s ∩ ⋃_i A_i ↔ x ∈ ⋃_i A_i ∩ s \\]
Lo demostramos mediante la siguiente cadena de equivalencias
\\begin{align}
   x ∈ s ∩ ⋃_i A_i &↔ x ∈ s ∧ x ∈ ⋃_i A_i \\\\
                   &↔ x ∈ s ∧ (∃ i)[x ∈ A_i] \\\\
                   &↔ (∃ i)[x ∈ s ∧ x ∈ A_i] \\\\
                   &↔ (∃ i)[x ∈ A_i ∧ x ∈ s] \\\\
                   &↔ (∃ i)[x ∈ A_i ∩ s] \\\\
                   &↔ x ∈ ⋃_i (A i ∩ s)
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s : Set α)
variable (A : ℕ → Set α)

-- 1ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  calc x ∈ s ∩ ⋃ (i : ℕ), A i
     ↔ x ∈ s ∧ x ∈ ⋃ (i : ℕ), A i :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ s ∧ (∃ i : ℕ, x ∈ A i) :=
         by simp only [mem_iUnion]
   _ ↔ ∃ i : ℕ, x ∈ s ∧ x ∈ A i :=
         by simp only [exists_and_left]
   _ ↔ ∃ i : ℕ, x ∈ A i ∧ x ∈ s :=
         by simp only [and_comm]
   _ ↔ ∃ i : ℕ, x ∈ A i ∩ s :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ ⋃ (i : ℕ), A i ∩ s :=
         by simp only [mem_iUnion]

-- 2ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  constructor
  . -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i → x ∈ ⋃ (i : ℕ), A i ∩ s
    intro h
    -- h : x ∈ s ∩ ⋃ (i : ℕ), A i
    -- ⊢ x ∈ ⋃ (i : ℕ), A i ∩ s
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ A i ∩ s
    rcases h with ⟨xs, xUAi⟩
    -- xs : x ∈ s
    -- xUAi : x ∈ ⋃ (i : ℕ), A i
    rw [mem_iUnion] at xUAi
    -- xUAi : ∃ i, x ∈ A i
    rcases xUAi with ⟨i, xAi⟩
    -- i : ℕ
    -- xAi : x ∈ A i
    use i
    -- ⊢ x ∈ A i ∩ s
    constructor
    . -- ⊢ x ∈ A i
      exact xAi
    . -- ⊢ x ∈ s
      exact xs
  . -- ⊢ x ∈ ⋃ (i : ℕ), A i ∩ s → x ∈ s ∩ ⋃ (i : ℕ), A i
    intro h
    -- h : x ∈ ⋃ (i : ℕ), A i ∩ s
    -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i
    rw [mem_iUnion] at h
    -- h : ∃ i, x ∈ A i ∩ s
    rcases h with ⟨i, hi⟩
    -- i : ℕ
    -- hi : x ∈ A i ∩ s
    rcases hi with ⟨xAi, xs⟩
    -- xAi : x ∈ A i
    -- xs : x ∈ s
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ⊢ x ∈ ⋃ (i : ℕ), A i
      rw [mem_iUnion]
      -- ⊢ ∃ i, x ∈ A i
      use i
      -- ⊢ x ∈ A i
      exact xAi

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  simp
  -- ⊢ (x ∈ s ∧ ∃ i, x ∈ A i) ↔ (∃ i, x ∈ A i) ∧ x ∈ s
  constructor
  . -- ⊢ (x ∈ s ∧ ∃ i, x ∈ A i) → (∃ i, x ∈ A i) ∧ x ∈ s
    rintro ⟨xs, ⟨i, xAi⟩⟩
    -- xs : x ∈ s
    -- i : ℕ
    -- xAi : x ∈ A i
    -- ⊢ (∃ i, x ∈ A i) ∧ x ∈ s
    exact ⟨⟨i, xAi⟩, xs⟩
  . -- ⊢ (∃ i, x ∈ A i) ∧ x ∈ s → x ∈ s ∧ ∃ i, x ∈ A i
    rintro ⟨⟨i, xAi⟩, xs⟩
    -- xs : x ∈ s
    -- i : ℕ
    -- xAi : x ∈ A i
    -- ⊢ x ∈ s ∧ ∃ i, x ∈ A i
    exact ⟨xs, ⟨i, xAi⟩⟩

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ ⋃ (i : ℕ), A i ↔ x ∈ ⋃ (i : ℕ), A i ∩ s
  aesop

-- 4ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by ext; aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (t : Set α)
-- variable (a b : Prop)
-- variable (p : α → Prop)
-- #check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
-- #check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
-- #check (exists_and_left : (∃ (x : α), b ∧ p x) ↔ b ∧ ∃ (x : α), p x)
-- #check (and_comm : a ∧ b ↔ b ∧ a)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Distributiva_de_la_interseccion_respecto_de_la_union_general.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Distributiva_de_la_interseccion_respecto_de_la_union_general
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ (⋃ i ∈ I. A i) = (⋃ i ∈ I. (A i ∩ s))"
proof (rule equalityI)
  show "s ∩ (⋃ i ∈ I. A i) ⊆ (⋃ i ∈ I. (A i ∩ s))"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∩ (⋃ i ∈ I. A i)"
    then have "x ∈ s"
      by (simp only: IntD1)
    have "x ∈ (⋃ i ∈ I. A i)"
      using ‹x ∈ s ∩ (⋃ i ∈ I. A i)› by (simp only: IntD2)
    then show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "x ∈ A i"
      then have "x ∈ A i ∩ s"
        using ‹x ∈ s› by (rule IntI)
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
        by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. (A i ∩ s)) ⊆ s ∩ (⋃ i ∈ I. A i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (⋃ i ∈ I. A i ∩ s)"
    then show "x ∈ s ∩ (⋃ i ∈ I. A i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "x ∈ A i ∩ s"
      then have "x ∈ A i"
        by (rule IntD1)
      have "x ∈ s"
        using ‹x ∈ A i ∩ s› by (rule IntD2)
      moreover
      have "x ∈ (⋃ i ∈ I. A i)"
        using ‹i ∈ I› ‹x ∈ A i› by (rule UN_I)
      ultimately show "x ∈ s ∩ (⋃ i ∈ I. A i)"
        by (rule IntI)
    qed
  qed
qed

(* 2ª demostración *)
lemma "s ∩ (⋃ i ∈ I. A i) = (⋃ i ∈ I. (A i ∩ s))"
proof
  show "s ∩ (⋃ i ∈ I. A i) ⊆ (⋃ i ∈ I. (A i ∩ s))"
  proof
    fix x
    assume "x ∈ s ∩ (⋃ i ∈ I. A i)"
    then have "x ∈ s"
      by simp
    have "x ∈ (⋃ i ∈ I. A i)"
      using ‹x ∈ s ∩ (⋃ i ∈ I. A i)› by simp
    then show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
    proof
      fix i
      assume "i ∈ I"
      assume "x ∈ A i"
      then have "x ∈ A i ∩ s"
        using ‹x ∈ s› by simp
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. (A i ∩ s))"
        by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. (A i ∩ s)) ⊆ s ∩ (⋃ i ∈ I. A i)"
  proof
    fix x
    assume "x ∈ (⋃ i ∈ I. A i ∩ s)"
    then show "x ∈ s ∩ (⋃ i ∈ I. A i)"
    proof
      fix i
      assume "i ∈ I"
      assume "x ∈ A i ∩ s"
      then have "x ∈ A i"
        by simp
      have "x ∈ s"
        using ‹x ∈ A i ∩ s› by simp
      moreover
      have "x ∈ (⋃ i ∈ I. A i)"
        using ‹i ∈ I› ‹x ∈ A i› by (rule UN_I)
      ultimately show "x ∈ s ∩ (⋃ i ∈ I. A i)"
        by simp
    qed
  qed
qed

(* 3ª demostración *)
lemma "s ∩ (⋃ i ∈ I. A i) = (⋃ i ∈ I. (A i ∩ s))"
  by auto

end
</pre>
