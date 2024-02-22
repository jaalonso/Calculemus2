---
Título: (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set
variable {α : Type}
variable (s t u : Set α)

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ (s ∩ t) ∪ (s ∩ u)\\). Entonces son posibles dos casos.

1º caso: Supongamos que \\(x ∈ s ∩ t\\). Entonces, \\(x ∈ s\\) y \\(x ∈ t\\) (y, por tanto, \\(x ∈ t ∪ u\\)). Luego, \\(x ∈ s ∩ (t ∪ u)\\).

2º caso: Supongamos que \\(x ∈ s ∩ u\\). Entonces, \\(x ∈ s\\) y \\(x ∈ u\\) (y, por tanto, \\(x ∈ t ∪ u\\)). Luego, \\(x ∈ s ∩ (t ∪ u)\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ t ∪ s ∩ u
  -- ⊢ x ∈ s ∩ (t ∪ u)
  rcases hx with (xst | xsu)
  . -- xst : x ∈ s ∩ t
    constructor
    . -- ⊢ x ∈ s
      exact xst.1
    . -- ⊢ x ∈ t ∪ u
      left
      -- ⊢ x ∈ t
      exact xst.2
  . -- xsu : x ∈ s ∩ u
    constructor
    . -- ⊢ x ∈ s
      exact xsu.1
    . -- ⊢ x ∈ t ∪ u
      right
      -- ⊢ x ∈ u
      exact xsu.2

-- 2ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  . -- x : α
    -- xs : x ∈ s
    -- xt : x ∈ t
    -- ⊢ x ∈ s ∩ (t ∪ u)
    use xs
    -- ⊢ x ∈ t ∪ u
    left
    -- ⊢ x ∈ t
    exact xt
  . -- x : α
    -- xs : x ∈ s
    -- xu : x ∈ u
    -- ⊢ x ∈ s ∩ (t ∪ u)
    use xs
    -- ⊢ x ∈ t ∪ u
    right
    -- ⊢ x ∈ u
    exact xu

-- 3ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by rw [inter_distrib_left s t u]

-- 4ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ t ∪ s ∩ u
  -- ⊢ x ∈ s ∩ (t ∪ u)
  aesop
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2
imports Main
begin

(* 1ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof (rule subsetI)
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
  proof (rule UnE)
    assume xst : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ t"
      using xst by (simp only: IntD2)
    then have xtu : "x ∈ t ∪ u"
      by (simp only: UnI1)
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by (simp only: IntI)
  next
    assume xsu : "x ∈ s ∩ u"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ u"
      using xsu by (simp only: IntD2)
    then have xtu : "x ∈ t ∪ u"
      by (simp only: UnI2)
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by (simp only: IntI)
  qed
qed

(* 2ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
  proof
    assume xst : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by simp
    have xt : "x ∈ t"
      using xst by simp
    then have xtu : "x ∈ t ∪ u"
      by simp
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by simp
  next
    assume xsu : "x ∈ s ∩ u"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ u"
      using xsu by simp
    then have xtu : "x ∈ t ∪ u"
      by simp
    show "x ∈ s ∩ (t ∪ u)"
      using xs xtu by simp
  qed
qed

(* 3ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
  proof
    assume "x ∈ s ∩ t"
    then show "x ∈ s ∩ (t ∪ u)"
      by simp
  next
    assume "x ∈ s ∩ u"
    then show "x ∈ s ∩ (t ∪ u)"
      by simp
  qed
qed

(* 4ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
proof
  fix x
  assume "x ∈ (s ∩ t) ∪ (s ∩ u)"
  then show "x ∈ s ∩ (t ∪ u)"
    by auto
qed

(* 5ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
by auto

(* 6ª demostración *)
lemma "(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)"
by (simp only: distrib_inf_le)

end
</pre>
