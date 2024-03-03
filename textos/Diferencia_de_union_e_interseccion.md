---
Título: (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ (s \\setminus t) ∪ (t \\setminus s) = (s ∪ t) \\setminus (s ∩ t) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

example : (s \\ t) ∪ (t \\ s) = (s ∪ t) \\ (s ∩ t) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que, para todo \\(x\\),
\\[ x ∈ (s \\setminus t) ∪ (t \\setminus s) ↔ x ∈ (s ∪ t) \\setminus (s ∩ t) \\]
Se demuestra mediante la siguiente cadena de equivalencias:
\\begin{align}
     &x ∈ (s \\setminus t) ∪ (t \\setminus s) \\\\
   ↔ &x ∈ (s \\setminus t) ∨ x ∈ (t \\setminus s) \\\\
   ↔ &(x ∈ s ∧ x ∉ t) ∨ x ∈ (t \\setminus s) \\\\
   ↔ &(x ∈ s ∨ x ∈ (t \\ s)) ∧ (x ∉ t ∨ x ∈ (t \\setminus s)) \\\\
   ↔ &(x ∈ s ∨ (x ∈ t ∧ x ∉ s)) ∧ (x ∉ t ∨ (x ∈ t ∧ x ∉ s)) \\\\
   ↔ &((x ∈ s ∨ x ∈ t) ∧ (x ∈ s ∨ x ∉ s)) ∧ ((x ∉ t ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s)) \\\\
   ↔ &(x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s) \\\\
   ↔ &(x ∈ s ∪ t) ∧ (x ∉ t ∨ x ∉ s) \\\\
   ↔ &(x ∈ s ∪ t) ∧ (x ∉ s ∨ x ∉ t) \\\\
   ↔ &(x ∈ s ∪ t) ∧ ¬(x ∈ s ∧ x ∈ t) \\\\
   ↔ &(x ∈ s ∪ t) ∧ ¬(x ∈ s ∩ t) \\\\
   ↔ &x ∈ (s ∪ t) \\setminus (s ∩ t)
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  calc x ∈ (s \ t) ∪ (t \ s)
     ↔ x ∈ (s \ t) ∨ x ∈ (t \ s) :=
         by exact mem_union x (s \ t) (t \ s)
   _ ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ (t \ s) :=
         by simp only [mem_diff]
   _ ↔ (x ∈ s ∨ x ∈ (t \ s)) ∧ (x ∉ t ∨ x ∈ (t \ s)) :=
         by exact and_or_right
   _ ↔ (x ∈ s ∨ (x ∈ t ∧ x ∉ s)) ∧ (x ∉ t ∨ (x ∈ t ∧ x ∉ s)) :=
         by simp only [mem_diff]
   _ ↔ ((x ∈ s ∨ x ∈ t) ∧ (x ∈ s ∨ x ∉ s)) ∧
       ((x ∉ t ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s)) :=
         by simp_all only [or_and_left]
   _ ↔ ((x ∈ s ∨ x ∈ t) ∧ True) ∧
       (True ∧ (x ∉ t ∨ x ∉ s)) :=
         by simp only [em (x ∈ s), em' (x ∈ t)]
   _ ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∉ s) :=
         by simp only [and_true_iff (x ∈ s ∨ x ∈ t),
                       true_and_iff (¬x ∈ t ∨ ¬x ∈ s)]
   _ ↔ (x ∈ s ∪ t) ∧ (x ∉ t ∨ x ∉ s) :=
         by simp only [mem_union]
   _ ↔ (x ∈ s ∪ t) ∧ (x ∉ s ∨ x ∉ t) :=
         by simp only [or_comm]
   _ ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∧ x ∈ t) :=
         by simp only [not_and_or]
   _ ↔ (x ∈ s ∪ t) ∧ ¬(x ∈ s ∩ t) :=
         by simp only [mem_inter_iff]
   _ ↔ x ∈ (s ∪ t) \ (s ∩ t)     :=
         by simp only [mem_diff]

-- 2ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . -- xs : x ∈ s
      -- xnt : ¬x ∈ t
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      constructor
      . -- ⊢ x ∈ s ∪ t
        left
        -- ⊢ x ∈ s
        exact xs
      . -- ⊢ ¬x ∈ s ∩ t
        rintro ⟨-, xt⟩
        -- xt : x ∈ t
        -- ⊢ False
        exact xnt xt
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      constructor
      . -- ⊢ x ∈ s ∪ t
        right
        -- ⊢ x ∈ t
        exact xt
      . -- ⊢ ¬x ∈ s ∩ t
        rintro ⟨xs, -⟩
        -- xs : x ∈ s
        -- ⊢ False
        exact xns xs
  . -- ⊢ x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s)
    rintro ⟨xs | xt, nxst⟩
    . -- xs : x ∈ s
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      left
      -- ⊢ x ∈ s \ t
      use xs
      -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply nxst
      -- ⊢ x ∈ s ∩ t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ t
        exact xt
    . -- nxst : ¬x ∈ s ∩ t
      -- xt : x ∈ t
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      right
      -- ⊢ x ∈ t \ s
      use xt
      -- ⊢ ¬x ∈ s
      intro xs
      -- xs : x ∈ s
      -- ⊢ False
      apply nxst
      -- ⊢ x ∈ s ∩ t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ t
        exact xt

-- 3ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      aesop
    . -- xt : x ∈ t
      -- xns : ¬x ∈ s
      -- ⊢ x ∈ (s ∪ t) \ (s ∩ t)
      aesop
  . rintro ⟨xs | xt, nxst⟩
    . -- xs : x ∈ s
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      aesop
    . -- nxst : ¬x ∈ s ∩ t
      -- xt : x ∈ t
      -- ⊢ x ∈ (s \ t) ∪ (t \ s)
      aesop

-- 4ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)
    rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩) <;> aesop
  . -- ⊢ x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s)
    rintro ⟨xs | xt, nxst⟩ <;> aesop

-- 5ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext
  constructor
  . aesop
  . aesop

-- 6ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext
  constructor <;> aesop

-- 7ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  rw [ext_iff]
  -- ⊢ ∀ (x : α), x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  intro
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ (t \ s) ↔ x ∈ (s ∪ t) \ (s ∩ t)
  rw [iff_def]
  -- ⊢ (x ∈ (s \ t) ∪ (t \ s) → x ∈ (s ∪ t) \ (s ∩ t)) ∧
  --   (x ∈ (s ∪ t) \ (s ∩ t) → x ∈ (s \ t) ∪ (t \ s))
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b c : Prop)
-- #check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
-- #check (mem_diff x : x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t)
-- #check (and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c))
-- #check (or_and_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c))
-- #check (em a : a ∨ ¬ a)
-- #check (em' a : ¬ a ∨ a)
-- #check (and_true_iff a : a ∧ True ↔ a)
-- #check (true_and_iff a : True ∧ a ↔ a)
-- #check (or_comm : a ∨ b ↔ b ∨ a)
-- #check (not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b)
-- #check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
-- #check (ext_iff : s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
-- #check (iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a))
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Diferencia_de_union_e_interseccion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Diferencia_de_union_e_interseccion
imports Main
begin

(* 1 demostración *)
lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof (rule equalityI)
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)"
    proof (rule UnE)
      assume "x ∈ s - t"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof (rule DiffE)
        assume "x ∈ s"
        assume "x ∉ t"
        have "x ∈ s ∪ t"
          using ‹x ∈ s› by (simp only: UnI1)
        moreover
        have "x ∉ s ∩ t"
        proof (rule notI)
          assume "x ∈ s ∩ t"
          then have "x ∈ t"
            by (simp only: IntD2)
          with ‹x ∉ t› show False
            by (rule notE)
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by (rule DiffI)
      qed
    next
      assume "x ∈ t - s"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof (rule DiffE)
        assume "x ∈ t"
        assume "x ∉ s"
        have "x ∈ s ∪ t"
          using ‹x ∈ t› by (simp only: UnI2)
        moreover
        have "x ∉ s ∩ t"
        proof (rule notI)
          assume "x ∈ s ∩ t"
          then have "x ∈ s"
            by (simp only: IntD1)
          with ‹x ∉ s› show False
            by (rule notE)
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by (rule DiffI)
      qed
    qed
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)"
    proof (rule DiffE)
      assume "x ∈ s ∪ t"
      assume "x ∉ s ∩ t"
      note ‹x ∈ s ∪ t›
      then show "x ∈ (s - t) ∪ (t - s)"
      proof (rule UnE)
        assume "x ∈ s"
        have "x ∉ t"
        proof (rule notI)
          assume "x ∈ t"
          with ‹x ∈ s› have "x ∈ s ∩ t"
            by (rule IntI)
          with ‹x ∉ s ∩ t› show False
            by (rule notE)
        qed
        with ‹x ∈ s› have "x ∈ s - t"
          by (rule DiffI)
        then show "x ∈ (s - t) ∪ (t - s)"
          by (simp only: UnI1)
      next
        assume "x ∈ t"
        have "x ∉ s"
        proof (rule notI)
          assume "x ∈ s"
          then have "x ∈ s ∩ t"
            using ‹x ∈ t› by (rule IntI)
          with ‹x ∉ s ∩ t› show False
            by (rule notE)
        qed
        with ‹x ∈ t› have "x ∈ t - s"
          by (rule DiffI)
        then show "x ∈ (s - t) ∪ (t - s)"
          by (rule UnI2)
      qed
    qed
  qed
qed

(* 2 demostración *)
lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)"
    proof
      assume "x ∈ s - t"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof
        assume "x ∈ s"
        assume "x ∉ t"
        have "x ∈ s ∪ t"
          using ‹x ∈ s› by simp
        moreover
        have "x ∉ s ∩ t"
        proof
          assume "x ∈ s ∩ t"
          then have "x ∈ t"
            by simp
          with ‹x ∉ t› show False
            by simp
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by simp
      qed
    next
      assume "x ∈ t - s"
      then show "x ∈ (s ∪ t) - (s ∩ t)"
      proof
        assume "x ∈ t"
        assume "x ∉ s"
        have "x ∈ s ∪ t"
          using ‹x ∈ t› by simp
        moreover
        have "x ∉ s ∩ t"
        proof
          assume "x ∈ s ∩ t"
          then have "x ∈ s"
            by simp
          with ‹x ∉ s› show False
            by simp
        qed
        ultimately show "x ∈ (s ∪ t) - (s ∩ t)"
          by simp
      qed
    qed
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)"
    proof
      assume "x ∈ s ∪ t"
      assume "x ∉ s ∩ t"
      note ‹x ∈ s ∪ t›
      then show "x ∈ (s - t) ∪ (t - s)"
      proof
        assume "x ∈ s"
        have "x ∉ t"
        proof
          assume "x ∈ t"
          with ‹x ∈ s› have "x ∈ s ∩ t"
            by simp
          with ‹x ∉ s ∩ t› show False
            by simp
        qed
        with ‹x ∈ s› have "x ∈ s - t"
          by simp
        then show "x ∈ (s - t) ∪ (t - s)"
          by simp
      next
        assume "x ∈ t"
        have "x ∉ s"
        proof
          assume "x ∈ s"
          then have "x ∈ s ∩ t"
            using ‹x ∈ t› by simp
          with ‹x ∉ s ∩ t› show False
            by simp
        qed
        with ‹x ∈ t› have "x ∈ t - s"
          by simp
        then show "x ∈ (s - t) ∪ (t - s)"
          by simp
      qed
    qed
  qed
qed

(* 3ª demostración *)
lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)"
    proof
      assume "x ∈ s - t"
      then show "x ∈ (s ∪ t) - (s ∩ t)" by simp
    next
      assume "x ∈ t - s"
      then show "x ∈ (s ∪ t) - (s ∩ t)" by simp
    qed
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)"
    proof
      assume "x ∈ s ∪ t"
      assume "x ∉ s ∩ t"
      note ‹x ∈ s ∪ t›
      then show "x ∈ (s - t) ∪ (t - s)"
      proof
        assume "x ∈ s"
        then show "x ∈ (s - t) ∪ (t - s)"
          using ‹x ∉ s ∩ t› by simp
      next
        assume "x ∈ t"
        then show "x ∈ (s - t) ∪ (t - s)"
          using ‹x ∉ s ∩ t› by simp
      qed
    qed
  qed
qed

(* 4ª demostración *)

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)"
  proof
    fix x
    assume "x ∈ (s - t) ∪ (t - s)"
    then show "x ∈ (s ∪ t) - (s ∩ t)" by auto
  qed
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)"
  proof
    fix x
    assume "x ∈ (s ∪ t) - (s ∩ t)"
    then show "x ∈ (s - t) ∪ (t - s)" by auto
  qed
qed

(* 5ª demostración *)

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
proof
  show "(s - t) ∪ (t - s) ⊆ (s ∪ t) - (s ∩ t)" by auto
next
  show "(s ∪ t) - (s ∩ t) ⊆ (s - t) ∪ (t - s)" by auto
qed

(* 6ª demostración *)

lemma "(s - t) ∪ (t - s) = (s ∪ t) - (s ∩ t)"
  by auto

end
</pre>
