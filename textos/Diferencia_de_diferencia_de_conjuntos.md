---
Título: (s \ t) \ u ⊆ s \ (t ∪ u)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ (s \setminus t) \setminus u ⊆ s \setminus (t ∪ u) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set
variable {α : Type}
variable (s t u : Set α)

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ (s \setminus t) \setminus u\\). Entonces, se tiene que
\\begin{align}
   &x ∈ s \\tag{1} \\\\
   &x ∉ t \\tag{2} \\\\
   &x ∉ u \\tag{3}
\\end{align}
Tenemos que demostrar que
\\[ x ∈ s \setminus (t ∪ u) \\]
pero, por (1), se reduce a
\\[ x ∉ t ∪ u \\]
que se verifica por (2) y (3).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ (s \ t) \ u
  -- ⊢ x ∈ s \ (t ∪ u)
  rcases hx with ⟨hxst, hxnu⟩
  -- hxst : x ∈ s \ t
  -- hxnu : ¬x ∈ u
  rcases hxst with ⟨hxs, hxnt⟩
  -- hxs : x ∈ s
  -- hxnt : ¬x ∈ t
  constructor
  . -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ ¬x ∈ t ∪ u
    by_contra hxtu
    -- hxtu : x ∈ t ∪ u
    -- ⊢ False
    rcases hxtu with (hxt | hxu)
    . -- hxt : x ∈ t
      apply hxnt
      -- ⊢ x ∈ t
      exact hxt
    . -- hxu : x ∈ u
      apply hxnu
      -- ⊢ x ∈ u
      exact hxu

-- 2ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  rintro x ⟨⟨hxs, hxnt⟩, hxnu⟩
  -- x : α
  -- hxnu : ¬x ∈ u
  -- hxs : x ∈ s
  -- hxnt : ¬x ∈ t
  -- ⊢ x ∈ s \ (t ∪ u)
  constructor
  . -- ⊢ x ∈ s
    exact hxs
  . -- ⊢ ¬x ∈ t ∪ u
    by_contra hxtu
    -- hxtu : x ∈ t ∪ u
    -- ⊢ False
    rcases hxtu with (hxt | hxu)
    . -- hxt : x ∈ t
      exact hxnt hxt
    . -- hxu : x ∈ u
      exact hxnu hxu

-- 3ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  -- x : α
  -- xnu : ¬x ∈ u
  -- xs : x ∈ s
  -- xnt : ¬x ∈ t
  -- ⊢ x ∈ s \ (t ∪ u)
  use xs
  -- ⊢ ¬x ∈ t ∪ u
  rintro (xt | xu)
  . -- xt : x ∈ t
    -- ⊢ False
    contradiction
  . -- xu : x ∈ u
    -- ⊢ False
    contradiction

-- 4ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  -- x : α
  -- xnu : ¬x ∈ u
  -- xs : x ∈ s
  -- xnt : ¬x ∈ t
  -- ⊢ x ∈ s \ (t ∪ u)
  use xs
  -- ⊢ ¬x ∈ t ∪ u
  rintro (xt | xu) <;> contradiction

-- 5ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  intro x xstu
  -- x : α
  -- xstu : x ∈ (s \ t) \ u
  -- ⊢ x ∈ s \ (t ∪ u)
  simp at *
  -- ⊢ x ∈ s ∧ ¬(x ∈ t ∨ x ∈ u)
  aesop

-- 6ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by
  intro x xstu
  -- x : α
  -- xstu : x ∈ (s \ t) \ u
  -- ⊢ x ∈ s \ (t ∪ u)
  aesop

-- 7ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by rw [diff_diff]

-- Lema usado
-- ==========

-- #check (diff_diff : (s \ t) \ u = s \ (t ∪ u))
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Diferencia_de_diferencia_de_conjuntos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Diferencia_de_diferencia_de_conjuntos
imports Main
begin

(* 1ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ (s - t) - u"
  then show "x ∈ s - (t ∪ u)"
  proof (rule DiffE)
    assume xst : "x ∈ s - t"
    assume xnu : "x ∉ u"
    note xst
    then show "x ∈ s - (t ∪ u)"
    proof (rule DiffE)
      assume xs : "x ∈ s"
      assume xnt : "x ∉ t"
      have xntu : "x ∉ t ∪ u"
      proof (rule notI)
        assume xtu : "x ∈ t ∪ u"
        then show False
        proof (rule UnE)
          assume xt : "x ∈ t"
          with xnt show False
            by (rule notE)
        next
          assume xu : "x ∈ u"
          with xnu show False
            by (rule notE)
        qed
      qed
      show "x ∈ s - (t ∪ u)"
        using xs xntu by (rule DiffI)
    qed
  qed
qed

(* 2ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
proof
  fix x
  assume hx : "x ∈ (s - t) - u"
  then have xst : "x ∈ (s - t)"
    by simp
  then have xs : "x ∈ s"
    by simp
  have xnt : "x ∉ t"
    using xst by simp
  have xnu : "x ∉ u"
    using hx by simp
  have xntu : "x ∉ t ∪ u"
    using xnt xnu by simp
  then show "x ∈ s - (t ∪ u)"
    using xs by simp
qed

(* 3ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
proof
  fix x
  assume "x ∈ (s - t) - u"
  then show "x ∈ s - (t ∪ u)"
     by simp
qed

(* 4ª demostración *)
lemma "(s - t) - u ⊆ s - (t ∪ u)"
by auto

end
</pre>
