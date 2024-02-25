---
Título: s ∩ t = t ∩ s
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ s ∩ t = t ∩ s \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set
variable {α : Type}
variable (s t : Set α)

example : s ∩ t = t ∩ s :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que
\\[ (∀ x)[x ∈ s ∩ t ↔ x ∈ t ∩ s] \\]
Demostratemos la equivalencia por la doble implicación.

Sea \\(x ∈ s ∩ t\\). Entonces, se tiene
\\begin{align}
   &x ∈ s \\tag{1} \\\\
   &x ∈ t \\tag{2}
\\end{align}
Luego \\(x ∈ t ∩ s\\) (por (2) y (1)).

La segunda implicación se demuestra análogamente.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
    intro h
    -- h : x ∈ s ∧ x ∈ t
    -- ⊢ x ∈ t ∧ x ∈ s
    constructor
    . -- ⊢ x ∈ t
      exact h.2
    . -- ⊢ x ∈ s
      exact h.1
  . -- ⊢ x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
    intro h
    -- h : x ∈ t ∧ x ∈ s
    -- ⊢ x ∈ s ∧ x ∈ t
    constructor
    . -- ⊢ x ∈ s
      exact h.2
    . -- ⊢ x ∈ t
      exact h.1

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  exact ⟨fun h ↦ ⟨h.2, h.1⟩,
         fun h ↦ ⟨h.2, h.1⟩⟩

-- 3ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  exact ⟨fun h ↦ ⟨h.2, h.1⟩,
         fun h ↦ ⟨h.2, h.1⟩⟩

-- 4ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
    rintro ⟨xs, xt⟩
    -- xs : x ∈ s
    -- xt : x ∈ t
    -- ⊢ x ∈ t ∧ x ∈ s
    exact ⟨xt, xs⟩
  . -- ⊢ x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
    rintro ⟨xt, xs⟩
    -- xt : x ∈ t
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∧ x ∈ t
    exact ⟨xs, xt⟩

-- 5ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  -- ⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  simp only [And.comm]

-- 6ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
ext (fun _ ↦ And.comm)

-- 7ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext ; simp [And.comm]

-- 8ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
inter_comm s t

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b : Prop)
-- #check (And.comm : a ∧ b ↔ b ∧ a)
-- #check (inter_comm s t : s ∩ t = t ∩ s)
-- #check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Conmutatividad_de_la_interseccion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Conmutatividad_de_la_interseccion
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ t = t ∩ s"
proof (rule set_eqI)
  fix x
  show "x ∈ s ∩ t ⟷ x ∈ t ∩ s"
  proof (rule iffI)
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ t"
      using h by (simp only: IntD2)
    then show "x ∈ t ∩ s"
      using xs by (rule IntI)
  next
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by (simp only: IntD1)
    have xs : "x ∈ s"
      using h by (simp only: IntD2)
    then show "x ∈ s ∩ t"
      using xt by (rule IntI)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ t = t ∩ s"
proof (rule set_eqI)
  fix x
  show "x ∈ s ∩ t ⟷ x ∈ t ∩ s"
  proof
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by simp
    have xt : "x ∈ t"
      using h by simp
    then show "x ∈ t ∩ s"
      using xs by simp
  next
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by simp
    have xs : "x ∈ s"
      using h by simp
    then show "x ∈ s ∩ t"
      using xt by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ t = t ∩ s"
proof (rule equalityI)
  show "s ∩ t ⊆ t ∩ s"
  proof (rule subsetI)
    fix x
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ t"
      using h by (simp only: IntD2)
    then show "x ∈ t ∩ s"
      using xs by (rule IntI)
  qed
next
  show "t ∩ s ⊆ s ∩ t"
  proof (rule subsetI)
    fix x
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by (simp only: IntD1)
    have xs : "x ∈ s"
      using h by (simp only: IntD2)
    then show "x ∈ s ∩ t"
      using xt by (rule IntI)
  qed
qed

(* 4ª demostración *)
lemma "s ∩ t = t ∩ s"
proof
  show "s ∩ t ⊆ t ∩ s"
  proof
    fix x
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by simp
    have xt : "x ∈ t"
      using h by simp
    then show "x ∈ t ∩ s"
      using xs by simp
  qed
next
  show "t ∩ s ⊆ s ∩ t"
  proof
    fix x
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by simp
    have xs : "x ∈ s"
      using h by simp
    then show "x ∈ s ∩ t"
      using xt by simp
  qed
qed

(* 5ª demostración *)
lemma "s ∩ t = t ∩ s"
proof
  show "s ∩ t ⊆ t ∩ s"
  proof
    fix x
    assume "x ∈ s ∩ t"
    then show "x ∈ t ∩ s"
      by simp
  qed
next
  show "t ∩ s ⊆ s ∩ t"
  proof
    fix x
    assume "x ∈ t ∩ s"
    then show "x ∈ s ∩ t"
      by simp
  qed
qed

(* 6ª demostración *)
lemma "s ∩ t = t ∩ s"
by (fact Int_commute)

(* 7ª demostración *)
lemma "s ∩ t = t ∩ s"
by (fact inf_commute)

(* 8ª demostración *)
lemma "s ∩ t = t ∩ s"
by auto

end
</pre>
