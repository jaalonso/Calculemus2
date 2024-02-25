---
Título: s \ (t ∪ u) ⊆ (s \ t) \ u
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ s \setminus (t ∪ u) ⊆ (s \setminus t) \setminus u \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set
variable {α : Type}
variable (s t u : Set α)

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ s \setminus (t ∪ u)\\). Entonces,
\\begin{align}
   &x ∈ s      \\tag{1} \\\\
   &x ∉ t ∪ u  \\tag{2} \\\\
\\end{align}
Tenemos que demostrar que \\(x ∈ (s \setminus t) \setminus u\\); es decir, que se verifican las relaciones
\\begin{align}
   &x ∈ s \setminus t \\tag{3} \\\\
   &x ∉ u     \\tag{4}
\\end{align}
Para demostrar (3) tenemos que demostrar las relaciones
\\begin{align}
   &x ∈ s \\tag{5} \\\\
   &x ∉ t \\tag{6}
\\end{align}
La (5) se tiene por la (1). Para demostrar la (6), supongamos que \\(x ∈ t\\); entonces, \\(x ∈ t ∪ u\\), en contracción con (2). Para demostrar la (4), supongamos que \\(x ∈ u\\); entonces, \\(x ∈ t ∪ u\\), en contracción con (2).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s \ (t ∪ u)
  -- ⊢ x ∈ (s \ t) \ u
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact hx.1
    . -- ⊢ ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      apply hx.2
      -- ⊢ x ∈ t ∪ u
      left
      -- ⊢ x ∈ t
      exact xt
  . -- ⊢ ¬x ∈ u
    intro xu
    -- xu : x ∈ u
    -- ⊢ False
    apply hx.2
    -- ⊢ x ∈ t ∪ u
    right
    -- ⊢ x ∈ u
    exact xu

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  rintro x ⟨xs, xntu⟩
  -- x : α
  -- xs : x ∈ s
  -- xntu : ¬x ∈ t ∪ u
  -- ⊢ x ∈ (s \ t) \ u
  constructor
  . -- ⊢ x ∈ s \ t
    constructor
    . -- ⊢ x ∈ s
      exact xs
    . -- ¬x ∈ t
      intro xt
      -- xt : x ∈ t
      -- ⊢ False
      exact xntu (Or.inl xt)
  . -- ⊢ ¬x ∈ u
    intro xu
    -- xu : x ∈ u
    -- ⊢ False
    exact xntu (Or.inr xu)

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
  fun _ ⟨xs, xntu⟩ ↦ ⟨⟨xs, fun xt ↦ xntu (Or.inl xt)⟩,
                      fun xu ↦ xntu (Or.inr xu)⟩

-- 4ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by
  rintro x ⟨xs, xntu⟩
  -- x : α
  -- xs : x ∈ s
  -- xntu : ¬x ∈ t ∪ u
  -- ⊢ x ∈ (s \ t) \ u
  aesop

-- 5ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by intro ; aesop

-- 6ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by rw [diff_diff]

-- Lema usado
-- ==========

-- #check (diff_diff : (s \ t) \ u = s \ (t ∪ u))
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Diferencia_de_diferencia_de_conjuntos_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Diferencia_de_diferencia_de_conjuntos_2
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
