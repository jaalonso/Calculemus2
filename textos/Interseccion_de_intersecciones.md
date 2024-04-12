---
Título: ⋂ᵢ (Aᵢ ∩ Bᵢ) = (⋂ᵢ Aᵢ) ∩ (⋂ᵢ Bᵢ)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ ⋂_i (A_i ∩ B_i) = (⋂_i A_i) ∩ (⋂_i B_i) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (A B : ℕ → Set α)

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que para \\(x\\) se verifica
\\[ x ∈ ⋂_i (A_i ∩ B_i) ↔ x ∈ (⋂_i A_i) ∩ (⋂_i B_i) \\]
Lo demostramos mediante la siguiente cadena de equivalencias
\\begin{align}
   x ∈ ⋂_i (A_i ∩ B_i) &↔ (∀ i)[x ∈ A_i ∩ B_i] \\\\
                       &↔ (∀ i)[x ∈ A_i ∧ x ∈ B_i] \\\\
                       &↔ (∀ i)[x ∈ A_i] ∧ (∀ i)[x ∈ B_i] \\\\
                       &↔ x ∈ (⋂_i A_i) ∧ x ∈ (⋂_i B_i) \\\\
                       &↔ x ∈ (⋂_i A_i) ∩ (⋂_i B_i)
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (A B : ℕ → Set α)

-- 1ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  calc x ∈ ⋂ i, A i ∩ B i
     ↔ ∀ i, x ∈ A i ∩ B i :=
         by exact mem_iInter
   _ ↔ ∀ i, x ∈ A i ∧ x ∈ B i :=
         by simp only [mem_inter_iff]
   _ ↔ (∀ i, x ∈ A i) ∧ (∀ i, x ∈ B i) :=
         by exact forall_and
   _ ↔ x ∈ (⋂ i, A i) ∧ x ∈ (⋂ i, B i) :=
         by simp only [mem_iInter]
   _ ↔ x ∈ (⋂ i, A i) ∩ ⋂ i, B i :=
         by simp only [mem_inter_iff]

-- 2ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  constructor
  . -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) → (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    intro h
    -- h : ∀ (i : ℕ), x ∈ A i ∧ x ∈ B i
    -- ⊢ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    constructor
    . -- ⊢ ∀ (i : ℕ), x ∈ A i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ A i
      exact (h i).1
    . -- ⊢ ∀ (i : ℕ), x ∈ B i
      intro i
      -- i : ℕ
      -- ⊢ x ∈ B i
      exact (h i).2
  . -- ⊢ ((∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i) → ∀ (i : ℕ), x ∈ A i ∧ x ∈ B i
    intros h i
    -- h : (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
    -- i : ℕ
    -- ⊢ x ∈ A i ∧ x ∈ B i
    rcases h with ⟨h1, h2⟩
    -- h1 : ∀ (i : ℕ), x ∈ A i
    -- h2 : ∀ (i : ℕ), x ∈ B i
    constructor
    . -- ⊢ x ∈ A i
      exact h1 i
    . -- ⊢ x ∈ B i
      exact h2 i

-- 3ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  exact ⟨fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩,
         fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2 i⟩⟩

-- 4ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by
  ext
  -- x : α
  -- ⊢ x ∈ ⋂ (i : ℕ), A i ∩ B i ↔ x ∈ (⋂ (i : ℕ), A i) ∩ ⋂ (i : ℕ), B i
  simp only [mem_inter_iff, mem_iInter]
  -- ⊢ (∀ (i : ℕ), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : ℕ), x ∈ A i) ∧ ∀ (i : ℕ), x ∈ B i
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b : Set α)
-- variable (ι : Sort v)
-- variable (s : ι → Set α)
-- variable (p q : α → Prop)
-- #check (forall_and : (∀ (x : α), p x ∧ q x) ↔ (∀ (x : α), p x) ∧ ∀ (x : α), q x)
-- #check (mem_iInter : x ∈ ⋂ (i : ι), s i ↔ ∀ (i : ι), x ∈ s i)
-- #check (mem_inter_iff x a b : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Interseccion_de_intersecciones.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Interseccion_de_intersecciones
imports Main
begin

(* 1ª demostración *)
lemma "(⋂ i ∈ I. A i ∩ B i) = (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
proof (rule equalityI)
  show "(⋂ i ∈ I. A i ∩ B i) ⊆ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
  proof (rule subsetI)
    fix x
    assume h1 : "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    have "x ∈ (⋂ i ∈ I. A i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with h1 have "x ∈ A i ∩ B i"
        by (rule INT_D)
      then show "x ∈ A i"
        by (rule IntD1)
    qed
    moreover
    have "x ∈ (⋂ i ∈ I. B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with h1 have "x ∈ A i ∩ B i"
        by (rule INT_D)
      then show "x ∈ B i"
        by (rule IntD2)
    qed
    ultimately show "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
      by (rule IntI)
  qed
next
  show "(⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. A i ∩ B i)"
  proof (rule subsetI)
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      have "x ∈ A i"
      proof -
        have "x ∈ (⋂ i ∈ I. A i)"
          using h2 by (rule IntD1)
        then show "x ∈ A i"
          using ‹i ∈ I› by (rule INT_D)
      qed
      moreover
      have "x ∈ B i"
      proof -
        have "x ∈ (⋂ i ∈ I. B i)"
          using h2 by (rule IntD2)
        then show "x ∈ B i"
          using ‹i ∈ I› by (rule INT_D)
      qed
      ultimately show "x ∈ A i ∩ B i"
        by (rule IntI)
    qed
  qed
qed

(* 2ª demostración *)
lemma "(⋂ i ∈ I. A i ∩ B i) = (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
proof
  show "(⋂ i ∈ I. A i ∩ B i) ⊆ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
  proof
    fix x
    assume h1 : "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    have "x ∈ (⋂ i ∈ I. A i)"
    proof
      fix i
      assume "i ∈ I"
      then show "x ∈ A i"
        using h1 by simp
    qed
    moreover
    have "x ∈ (⋂ i ∈ I. B i)"
    proof
      fix i
      assume "i ∈ I"
      then show "x ∈ B i"
        using h1 by simp
    qed
    ultimately show "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
      by simp
  qed
next
  show "(⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. A i ∩ B i)"
  proof
    fix x
    assume h2 : "x ∈ (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. A i ∩ B i)"
    proof
      fix i
      assume "i ∈ I"
      then have "x ∈ A i"
        using h2 by simp
      moreover
      have "x ∈ B i"
        using ‹i ∈ I› h2 by simp
      ultimately show "x ∈ A i ∩ B i"
        by simp
    qed
qed
qed

(* 3ª demostración *)
lemma "(⋂ i ∈ I. A i ∩ B i) = (⋂ i ∈ I. A i) ∩ (⋂ i ∈ I. B i)"
  by auto

end
</pre>
