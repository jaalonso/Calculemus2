---
Título: (P → Q) ↔ ¬P ∨ Q.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\[ (P → Q) ↔ ¬P ∨ Q \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable (P Q : Prop)

example
  : (P → Q) ↔ ¬P ∨ Q :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Demostraremos cada una de las implicaciones.

(==>) Supongamos que \(P → Q\). Distinguimos dos subcasos según el valor de \(P\).

Primer subcaso: suponemos \(P\). Entonces, tenemos \(Q\) (porque \(P → Q\)) y. por tanto, \(¬P ∨ Q\).

Segundo subcaso: suponemos \(¬P\). Entonces. tenemos \(¬P ∨ Q\).

(<==) Supongamos que \(¬P ∨ Q\) y \(P\) y tenemos que demostrar \(Q\). Distinguimos dos subcasos según \(¬P ∨ Q\).

Primer subcaso: Suponemos \(¬P\). Entonces tenemos una contradicción con \(P\).

Segundo subcaso: Suponemos \(Q\), que es lo que tenemos que demostrar.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
variable (P Q : Prop)

-- 1ª demostración
-- ===============

example
  : (P → Q) ↔ ¬P ∨ Q :=
by
  constructor
  . -- ⊢ (P → Q) → ¬P ∨ Q
    intro h1
    -- h1 : P → Q
    -- ⊢ ¬P ∨ Q
    by_cases h2 : P
    . -- h2 : P
      right
      -- ⊢ Q
      apply h1
      -- ⊢ P
      exact h2
    . -- h2 : ¬P
      left
      -- ⊢ ¬P
      exact h2
  . -- ⊢ ¬P ∨ Q → P → Q
    intros h3 h4
    -- h3 : ¬P ∨ Q
    -- h4 : P
    -- ⊢ Q
    rcases h3 with h3a | h3b
    . -- h : ¬P
      exact absurd h4 h3a
    . -- h : Q
      exact h3b
  done

-- 2ª demostración
-- ===============

example
  : (P → Q) ↔ ¬P ∨ Q :=
by
  constructor
  . -- ⊢ (P → Q) → ¬P ∨ Q
    intro h1
    -- h1 : P → Q
    -- ⊢ ¬P ∨ Q
    by_cases h2: P
    . -- h2 : P
      right
      -- ⊢ Q
      exact h1 h2
    . -- h2 : ¬P
      left
      -- ⊢ ¬P
      exact h2
  . -- ⊢ ¬P ∨ Q → P → Q
    intros h3 h4
    -- h3 : ¬P ∨ Q
    -- h4 : P
    -- ⊢ Q
    cases h3
    . -- h : ¬P
      contradiction
    . -- h : Q
      assumption
  done

-- 3ª demostración
-- ===============

example
  (P Q : Prop)
  : (P → Q) ↔ ¬P ∨ Q :=
imp_iff_not_or

-- 4ª demostración
-- ===============

example
  (P Q : Prop)
  : (P → Q) ↔ ¬P ∨ Q :=
by tauto
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Implicacion_mediante_disyuncion_y_negacion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h3>Referencias</h3>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 40.</li>
</ul>

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Implicacion_mediante_disyuncion_y_negacion
imports Main
begin

(* 1ª demostración *)
lemma "(P ⟶ Q) ⟷ (¬P ∨ Q)"
proof
  assume "P ⟶ Q"
  show "¬P ∨ Q"
  proof -
    have "¬P ∨ P" by (rule excluded_middle)
    then show "¬P ∨ Q"
    proof (rule disjE)
      assume "¬P"
      then show "¬P ∨ Q" by (rule disjI1)
    next
      assume 2: "P"
      with `P ⟶ Q` have "Q" by (rule mp)
      then show "¬P ∨ Q" by (rule disjI2)
    qed
  qed
next
  assume "¬P ∨ Q"
  show "P ⟶ Q"
  proof
    assume "P"
    note `¬P ∨ Q`
    then show "Q"
    proof (rule disjE)
      assume "¬P"
      then show Q using `P` by (rule notE)
    next
      assume "Q"
      then show "Q" by this
    qed
  qed
qed

(* 2ª demostración *)
lemma "(P ⟶ Q) ⟷ (¬P ∨ Q)"
proof
  assume "P ⟶ Q"
  show "¬P ∨ Q"
  proof -
    have "¬P ∨ P" by (rule excluded_middle)
    then show "¬P ∨ Q"
    proof
      assume "¬P"
      then show "¬P ∨ Q" ..
    next
      assume 2: "P"
      with `P ⟶ Q` have "Q" ..
      then show "¬P ∨ Q" ..
    qed
  qed
next
  assume "¬P ∨ Q"
  show "P ⟶ Q"
  proof
    assume "P"
    note `¬P ∨ Q`
    then show "Q"
    proof
      assume "¬P"
      then show Q using `P` ..
    next
      assume "Q"
      then show "Q" .
    qed
  qed
qed

(* 3ª demostración *)
lemma "(P ⟶ Q) ⟷ (¬P ∨ Q)"
  by simp

end
</pre>
