---
Título: s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que \\(s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set
variable {α : Type}
variable (s t u : Set α)

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ s ∩ (t ∪ u)\\). Entonces se tiene que
\\begin{align}
   &x ∈ s     \\tag{1} \\\\
   &x ∈ t ∪ u \\tag{2}
\\end{align}
La relación (2) da lugar a dos casos.

Caso 1: Supongamos que \\(x ∈ t\\). Entonces, por (1), \\(x ∈ s ∩ t\\) y, por tanto, \\(x ∈ (s ∩ t) ∪ (s ∩ u)\\).

Caso 2: Supongamos que \\(x ∈ u\\). Entonces, por (1), \\(x ∈ s ∩ u\\) y, por tanto, \\(x ∈ (s ∩ t) ∪ (s ∩ u)\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α : Type}
variable (s t u : Set α)

-- 1ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  intros x hx
  -- x : α
  -- hx : x ∈ s ∩ (t ∪ u)
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  rcases hx with ⟨hxs, hxtu⟩
  -- hxs : x ∈ s
  -- hxtu : x ∈ t ∪ u
  rcases hxtu with (hxt | hxu)
  . -- hxt : x ∈ t
    left
    -- ⊢ x ∈ s ∩ t
    constructor
    . -- ⊢ x ∈ s
      exact hxs
    . -- hxt : x ∈ t
      exact hxt
  . -- hxu : x ∈ u
    right
    -- ⊢ x ∈ s ∩ u
    constructor
    . -- ⊢ x ∈ s
      exact hxs
    . -- ⊢ x ∈ u
      exact hxu

-- 2ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  rintro x ⟨hxs, hxt | hxu⟩
  -- x : α
  -- hxs : x ∈ s
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  . -- hxt : x ∈ t
    left
    -- ⊢ x ∈ s ∩ t
    exact ⟨hxs, hxt⟩
  . -- hxu : x ∈ u
    right
    -- ⊢ x ∈ s ∩ u
    exact ⟨hxs, hxu⟩

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  rintro x ⟨hxs, hxt | hxu⟩
  -- x : α
  -- hxs : x ∈ s
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  . -- hxt : x ∈ t
    exact Or.inl ⟨hxs, hxt⟩
  . -- hxu : x ∈ u
    exact Or.inr ⟨hxs, hxu⟩

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by
  intro x hx
  -- x : α
  -- hx : x ∈ s ∩ (t ∪ u)
  -- ⊢ x ∈ s ∩ t ∪ s ∩ u
  aesop

-- 5ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw [inter_union_distrib_left]
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Propiedad_semidistributiva_de_la_interseccion_sobre_la_union
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by (simp only: IntD1)
  have xtu: "x ∈ t ∪ u"
    using hx
    by (simp only: IntD2)
  then have "x ∈ t ∨ x ∈ u"
    by (simp only: Un_iff)
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule disjE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI1)
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI2)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by simp
  have xtu: "x ∈ t ∪ u"
    using hx
    by simp
  then have "x ∈ t ∨ x ∈ u"
    by simp
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt
      by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu
      by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof (rule subsetI)
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by (simp only: IntD1)
  have xtu: "x ∈ t ∪ u"
    using hx
    by (simp only: IntD2)
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule UnE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt
      by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI1)
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu
      by (simp only: Int_iff)
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by (simp only: UnI2)
  qed
qed

(* 4ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
proof
  fix x
  assume hx : "x ∈ s ∩ (t ∪ u)"
  then have xs : "x ∈ s"
    by simp
  have xtu: "x ∈ t ∪ u"
    using hx
    by simp
  then show " x ∈ s ∩ t ∪ s ∩ u"
  proof (rule UnE)
    assume xt : "x ∈ t"
    have xst : "x ∈ s ∩ t"
      using xs xt
      by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  next
    assume xu : "x ∈ u"
    have xst : "x ∈ s ∩ u"
      using xs xu by simp
    then show "x ∈ (s ∩ t) ∪ (s ∩ u)"
      by simp
  qed
qed

(* 5ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
by (simp only: Int_Un_distrib)

(* 6ª demostración *)
lemma "s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)"
by auto

end
</pre>
