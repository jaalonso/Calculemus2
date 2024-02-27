---
Título: (s \ t) ∪ t = s ∪ t
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ (s \\setminus t) ∪ t = s ∪ t \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

example : (s \\setminus t) ∪ t = s ∪ t :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que
\\[ (∀ x)[x ∈ (s \\setminus t) ∪ t ↔ x ∈ s ∪ t] \\]
y lo demostraremos por la siguiente cadena de equivalencias:
\\begin{align}
   x ∈ (s \\setminus t) ∪ t
                   &↔ x ∈ (s \\setminus t) ∨ (x ∈ t)             \\\\
                   &↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ t           \\\\
                   &↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∈ t) \\\\
                   &↔ x ∈ s ∨ x ∈ t                     \\\\
                   &↔ x ∈ s ∪ t
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  calc x ∈ (s \ t) ∪ t
       ↔ x ∈ s \ t ∨ x ∈ t                 := mem_union x (s \ t) t
     _ ↔ (x ∈ s ∧ x ∉ t) ∨ x ∈ t           := by simp only [mem_diff x]
     _ ↔ (x ∈ s ∨ x ∈ t) ∧ (x ∉ t ∨ x ∈ t) := and_or_right
     _ ↔ (x ∈ s ∨ x ∈ t) ∧ True            := by simp only [em' (x ∈ t)]
     _ ↔ x ∈ s ∨ x ∈ t                     := and_true_iff (x ∈ s ∨ x ∈ t)
     _ ↔ x ∈ s ∪ t                         := (mem_union x s t).symm

-- 2ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ t → x ∈ s ∪ t
    intro hx
    -- hx : x ∈ (s \ t) ∪ t
    -- ⊢ x ∈ s ∪ t
    rcases hx with (xst | xt)
    . -- xst : x ∈ s \ t
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xst.1
    . -- xt : x ∈ t
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
    by_cases h : x ∈ t
    . -- h : x ∈ t
      intro _xst
      -- _xst : x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact h
    . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
      intro hx
      -- hx : x ∈ s ∪ t
      -- ⊢ x ∈ (s \ t) ∪ t
      rcases hx with (xs | xt)
      . -- xs : x ∈ s
        left
        -- ⊢ x ∈ s \ t
        constructor
        . -- ⊢ x ∈ s
          exact xs
        . -- ⊢ ¬x ∈ t
          exact h
      . -- xt : x ∈ t
        right
        -- ⊢ x ∈ t
        exact xt

-- 3ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ (s \ t) ∪ t ↔ x ∈ s ∪ t
  constructor
  . -- ⊢ x ∈ (s \ t) ∪ t → x ∈ s ∪ t
    rintro (⟨xs, -⟩ | xt)
    . -- xs : x ∈ s
      -- ⊢ x ∈ s ∪ t
      left
      -- ⊢ x ∈ s
      exact xs
    . -- xt : x ∈ t
      -- ⊢ x ∈ s ∪ t
      right
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
    by_cases h : x ∈ t
    . -- h : x ∈ t
      intro _xst
      -- _xst : x ∈ s ∪ t
      -- ⊢ x ∈ (s \ t) ∪ t
      right
      -- ⊢ x ∈ t
      exact h
    . -- ⊢ x ∈ s ∪ t → x ∈ (s \ t) ∪ t
      rintro (xs | xt)
      . -- xs : x ∈ s
        -- ⊢ x ∈ (s \ t) ∪ t
        left
        -- ⊢ x ∈ s \ t
        exact ⟨xs, h⟩
      . -- xt : x ∈ t
        -- ⊢ x ∈ (s \ t) ∪ t
        right
        -- ⊢ x ∈ t
        exact xt

-- 4ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
diff_union_self

-- 5ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s \ t ∪ t ↔ x ∈ s ∪ t
  simp

-- 6ª demostración
-- ===============

example : (s \ t) ∪ t = s ∪ t :=
by simp

-- Lemas usados
-- ============

-- variable (a b c : Prop)
-- variable (x : α)
-- #check (and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c))
-- #check (and_true_iff a : a ∧ True ↔ a)
-- #check (diff_union_self : (s \ t) ∪ t = s ∪ t)
-- #check (em' a : ¬a ∨ a)
-- #check (mem_diff x : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t)
-- #check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/(s \ t) ∪ t = s ∪ t." rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Union_con_su_diferencia
imports Main
begin

(* 1ª demostración *)
lemma "(s - t) ∪ t = s ∪ t"
proof (rule equalityI)
  show "(s - t) ∪ t ⊆ s ∪ t"
  proof (rule subsetI)
    fix x
    assume "x ∈ (s - t) ∪ t"
    then show "x ∈ s ∪ t"
    proof (rule UnE)
      assume "x ∈ s - t"
      then have "x ∈ s"
        by (simp only: DiffD1)
      then show "x ∈ s ∪ t"
        by (simp only: UnI1)
    next
      assume "x ∈ t"
      then show "x ∈ s ∪ t"
        by (simp only: UnI2)
    qed
  qed
next
  show "s ∪ t ⊆ (s - t) ∪ t"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∪ t"
    then show "x ∈ (s - t) ∪ t"
    proof (rule UnE)
      assume "x ∈ s"
      show "x ∈ (s - t) ∪ t"
      proof (cases ‹x ∈ t›)
        assume "x ∈ t"
        then show "x ∈ (s - t) ∪ t"
          by (simp only: UnI2)
      next
        assume "x ∉ t"
        with ‹x ∈ s› have "x ∈ s - t"
          by (rule DiffI)
        then show "x ∈ (s - t) ∪ t"
          by (simp only: UnI1)
      qed
    next
      assume "x ∈ t"
      then show "x ∈ (s - t) ∪ t"
        by (simp only: UnI2)
    qed
  qed
qed

(* 2ª demostración *)
lemma "(s - t) ∪ t = s ∪ t"
proof
  show "(s - t) ∪ t ⊆ s ∪ t"
  proof
    fix x
    assume "x ∈ (s - t) ∪ t"
    then show "x ∈ s ∪ t"
    proof
      assume "x ∈ s - t"
      then have "x ∈ s"
        by simp
      then show "x ∈ s ∪ t"
        by simp
    next
      assume "x ∈ t"
      then show "x ∈ s ∪ t"
        by simp
    qed
  qed
next
  show "s ∪ t ⊆ (s - t) ∪ t"
  proof
    fix x
    assume "x ∈ s ∪ t"
    then show "x ∈ (s - t) ∪ t"
    proof
      assume "x ∈ s"
      show "x ∈ (s - t) ∪ t"
      proof
        assume "x ∉ t"
        with ‹x ∈ s› show "x ∈ s - t"
          by simp
      qed
    next
      assume "x ∈ t"
      then show "x ∈ (s - t) ∪ t"
        by simp
    qed
  qed
qed

(* 3ª demostración *)
lemma "(s - t) ∪ t = s ∪ t"
by (fact Un_Diff_cancel2)

(* 4ª demostración *)
lemma "(s - t) ∪ t = s ∪ t"
  by auto

end
</pre>
