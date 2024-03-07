---
Título: s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\[ s ∩ ⋃_i A_i = ⋃_i (A_i ∩ s) \]

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

Tenemos que demostrar que para cada \(x\), se verifica que
\[ x ∈ s ∩ ⋃_i A_i ↔ x ∈ ⋃_i A_i ∩ s \]
Lo demostramos mediante la siguiente cadena de equivalencias
\begin{align}
   x ∈ s ∩ ⋃_i A_i &↔ x ∈ s ∧ x ∈ ⋃_i A_i \\
                   &↔ x ∈ s ∧ (∃ i)[x ∈ A_i] \\
                   &↔ (∃ i)[x ∈ s ∧ x ∈ A_i] \\
                   &↔ (∃ i)[x ∈ A_i ∧ x ∈ s] \\
                   &↔ (∃ i)[x ∈ A_i ∩ s] \\
                   &↔ x ∈ ⋃_i (A i ∩ s)
\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
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
