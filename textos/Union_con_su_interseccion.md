---
Título: s ∪ (s ∩ t) = s
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ s ∪ (s ∩ t) = s \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set
variable {α : Type}
variable (s t : Set α)

example : s ∪ (s ∩ t) = s :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que
\\[ (∀ x)[x ∈ s ∪ (s ∩ t) ↔ x ∈ s] \\]
y lo haremos demostrando las dos implicaciones.

(⟹) Sea \\(x ∈ s ∪ (s ∩ t)\\). Entonces, \\(x ∈ s\\) ó \\(x ∈ s ∩ t\\). En ambos casos, \\(x ∈ s\\).

(⟸) Sea \\(x ∈ s\\). Entonces, \\(x ∈ s ∩ t\\) y, por tanto, \\(x ∈ s ∪ (s ∩ t)\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Basic
open Set

variable {α : Type}
variable (s t : Set α)

-- 1ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ (s ∩ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∪ (s ∩ t) → x ∈ s
    intro hx
    -- hx : x ∈ s ∪ (s ∩ t)
    -- ⊢ x ∈ s
    rcases hx with (xs | xst)
    . -- xs : x ∈ s
      exact xs
    . -- xst : x ∈ s ∩ t
      exact xst.1
  . -- ⊢ x ∈ s → x ∈ s ∪ (s ∩ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∪ (s ∩ t)
    left
    -- ⊢ x ∈ s
    exact xs

-- 2ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ s ∩ t ↔ x ∈ s
  exact ⟨fun hx ↦ Or.elim hx id And.left,
         fun xs ↦ Or.inl xs⟩

-- 3ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ s ∪ (s ∩ t) ↔ x ∈ s
  constructor
  . -- ⊢ x ∈ s ∪ (s ∩ t) → x ∈ s
    rintro (xs | ⟨xs, -⟩) <;>
    -- xs : x ∈ s
    -- ⊢ x ∈ s
    exact xs
  . -- ⊢ x ∈ s → x ∈ s ∪ (s ∩ t)
    intro xs
    -- xs : x ∈ s
    -- ⊢ x ∈ s ∪ s ∩ t
    left
    -- ⊢ x ∈ s
    exact xs

-- 4ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
sup_inf_self

-- Lemas usados
-- ============

-- variable (a b c : Prop)
-- #check (And.left : a ∧ b → a)
-- #check (Or.elim : a ∨ b → (a → c) → (b → c) → c)
-- #check (sup_inf_self : s ∪ (s ∩ t) = s)
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Union_con_su_interseccion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Union_con_su_interseccion
imports Main
begin

(* 1ª demostración *)
lemma "s ∪ (s ∩ t) = s"
proof (rule equalityI)
  show "s ∪ (s ∩ t) ⊆ s"
  proof (rule subsetI)
    fix x
    assume "x ∈ s ∪ (s ∩ t)"
    then show "x ∈ s"
    proof
      assume "x ∈ s"
      then show "x ∈ s"
        by this
    next
      assume "x ∈ s ∩ t"
      then show "x ∈ s"
        by (simp only: IntD1)
    qed
  qed
next
  show "s ⊆ s ∪ (s ∩ t)"
  proof (rule subsetI)
    fix x
    assume "x ∈ s"
    then show "x ∈ s ∪ (s ∩ t)"
      by (simp only: UnI1)
  qed
qed

(* 2ª demostración *)
lemma "s ∪ (s ∩ t) = s"
proof
  show "s ∪ s ∩ t ⊆ s"
  proof
    fix x
    assume "x ∈ s ∪ (s ∩ t)"
    then show "x ∈ s"
    proof
      assume "x ∈ s"
      then show "x ∈ s"
        by this
    next
      assume "x ∈ s ∩ t"
      then show "x ∈ s"
        by simp
    qed
  qed
next
  show "s ⊆ s ∪ (s ∩ t)"
  proof
    fix x
    assume "x ∈ s"
    then show "x ∈ s ∪ (s ∩ t)"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∪ (s ∩ t) = s"
  by auto

end
</pre>
