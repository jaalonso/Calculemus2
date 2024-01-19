---
Título: ¬¬P → P
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\[ ¬¬P → P \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable (P : Prop)

example : ¬¬P → P :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Supongamos que
\[ ¬¬P  \tag{1} \]

Por el principio del tercio excluso, se tiene
\[ P ∨ ¬P \]
lo que da lugar a dos casos.

En el primer caso, se supone \(P\) que es lo que hay que demostrar.

En el primer caso, se supone \(¬P\) que es una contradicción con (1).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
variable (P : Prop)

-- 1ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  have h2 : P ∨ ¬ P := em P
  rcases h2 with h3 | h4
  . -- h3 : P
    exact h3
  . -- h4 : ¬P
    exfalso
    -- ⊢ False
    exact h1 h4

-- 2ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  rcases em P with h2 | h3
  . -- h2 : P
    exact h2
  . -- h3 : ¬P
    exact absurd h3 h1

-- 3ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  cases em P
  . -- h2 : P
    assumption
  . -- h3 : ¬P
    contradiction

-- 4ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h
  by_cases P
  . assumption
  . contradiction

-- 4ª demostración
-- ===============

example : ¬¬P → P :=
by
  intro h1
  -- h1 : ¬¬P
  -- ⊢ P
  by_contra h
  -- h : ¬P
  -- ⊢ False
  exact h1 h

-- 5ª demostración
-- ===============

example : ¬¬P → P :=
by tauto
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Eliminacion_de_la_doble_negacion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h3>Referencias</h3>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 40.</li>
</ul>

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Eliminacion_de_la_doble_negacion
  imports Main
begin

(* 1ª demostración *)
lemma "¬¬P ⟶ P"
proof
  assume h1 : "¬¬P"
  have "¬P ∨ P" by (rule excluded_middle)
  then show "P"
  proof
    assume "¬P"
    then show "P" using h1 by (simp only: notE)
  next
    assume "P"
    then show "P" .
  qed
qed

(* 2ª demostración *)
lemma "¬¬P ⟶ P"
proof
  assume h1 : "¬¬P"
  show "P"
  proof (rule ccontr)
    assume "¬P"
    then show False using h1 by simp
  qed
qed

(* 3ª demostración *)
lemma "¬¬P ⟶ P"
  by simp

end
</pre>
