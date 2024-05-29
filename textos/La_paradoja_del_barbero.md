---
title: La paradoja del barbero
date: 2024-05-29 06:00:00 UTC+02:00
category: Lógica de primer orden
has_math: true
---

[mathjax]

Demostrar con Lean4 la [paradoja del barbero](https://bit.ly/3eWyvVw); es decir, que no existe un hombre que afeite a todos los que no se afeitan a sí mismo y sólo a los que no se afeitan a sí mismo.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable (Hombre : Type)
variable (afeita : Hombre → Hombre → Prop)

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que
\\[ ¬((∃ x)(∀ y)[\\text{afeita}(x,y) ↔ ¬\\text{afeita}(y,y)]) \\]
Para ello, supongamos que
\\[ (∃ x)(∀ y)[\\text{afeita}(x,y) ↔ ¬\\text{afeita}(y,y)] \\tag{1} \\]
y tenemos que llegar a una contradicción.

Sea \\(b\\) un elemento que verifica (1); es decir,
\\[ (∀ y)[\\text{afeita}(b,y) ↔ ¬\\text{afeita}(y,y)] \\]
Entonces,
\\[ \\text{afeita}(b,b) ↔ ¬\\text{afeita}(b,b) \\]
que es una contradicción.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable (Hombre : Type)
variable (afeita : Hombre → Hombre → Prop)

-- 1ª demostración
-- ===============

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by
  intro h
  -- h : ∃ x, ∀ (y : Hombre), afeita x y ↔ ¬afeita y y
  -- ⊢ False
  cases' h with b hb
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  specialize hb b
  -- hb : afeita b b ↔ ¬afeita b b
  by_cases (afeita b b)
  . -- h : afeita b b
    apply absurd h
    -- ⊢ ¬afeita b b
    exact hb.mp h
  . -- h : ¬afeita b b
    apply h
    -- ⊢ afeita b b
    exact hb.mpr h

-- 2ª demostración
-- ===============

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by
  intro h
  -- h : ∃ x, ∀ (y : Hombre), afeita x y ↔ ¬afeita y y
  -- ⊢ False
  cases' h with b hb
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  specialize hb b
  -- hb : afeita b b ↔ ¬afeita b b
  by_cases (afeita b b)
  . -- h : afeita b b
    exact (hb.mp h) h
  . -- h : ¬afeita b b
    exact h (hb.mpr h)

-- 3ª demostración
-- ===============

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by
  intro h
  -- h : ∃ x, ∀ (y : Hombre), afeita x y ↔ ¬afeita y y
  -- ⊢ False
  cases' h with b hb
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  exact iff_not_self (hb b)

-- 4ª demostración
-- ===============

example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
by
  rintro ⟨b, hb⟩
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  -- ⊢ False
  exact iff_not_self (hb b)

-- 5ª demostración
-- ===============

example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
fun ⟨b, hb⟩ ↦ iff_not_self (hb b)

-- Lemas usados
-- ============

-- variable (p q : Prop)
-- #check (absurd : p → (¬p → q))
-- #check (iff_not_self : ¬(p ↔ ¬p))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_paradoja_del_barbero.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_paradoja_del_barbero
imports Main
begin

(* 1ª demostración *)

lemma
  "¬(∃ x::'H. ∀ y::'H. afeita x y ⟷ ¬ afeita y y)"
proof (rule notI)
  assume "∃ x. ∀ y. afeita x y ⟷ ¬ afeita y y"
  then obtain b where "∀ y. afeita b y ⟷ ¬ afeita y y"
    by (rule exE)
  then have h : "afeita b b ⟷ ¬ afeita b b"
    by (rule allE)
  show False
  proof (cases "afeita b b")
    assume "afeita b b"
    then have "¬ afeita b b"
      using h by (rule rev_iffD1)
    then show False
      using ‹afeita b b› by (rule notE)
  next
    assume "¬ afeita b b"
    then have "afeita b b"
      using h by (rule rev_iffD2)
    with ‹¬ afeita b b› show False
      by (rule notE)
  qed
qed

(* 2ª demostración *)

lemma
  "¬(∃ x::'H. ∀ y::'H. afeita x y ⟷ ¬ afeita y y)"
proof
  assume "∃ x. ∀ y. afeita x y ⟷ ¬ afeita y y"
  then obtain b where "∀ y. afeita b y ⟷ ¬ afeita y y"
    by (rule exE)
  then have h : "afeita b b ⟷ ¬ afeita b b"
    by (rule allE)
  then show False
    by simp
qed

(* 3ª demostración *)

lemma
  "¬(∃ x::'H. ∀ y::'H. afeita x y ⟷ ¬ afeita y y)"
  by auto

end
</pre>
