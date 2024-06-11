---
title: Las funciones con inversa por la derecha son suprayectivas
date: 2024-06-12 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

En Lean4, que \\(g\\) es una inversa por la izquierda de \\(f\\) está definido por
<pre lang="haskell">
   LeftInverse (g : β → α) (f : α → β) : Prop :=
      ∀ x, g (f x) = x
</pre>
que \\(g\\) es una inversa por la derecha de \\(f\\) está definido por
<pre lang="haskell">
   RightInverse (g : β → α) (f : α → β) : Prop :=
      LeftInverse f g
</pre>
y que \\(f\\) tenga inversa por la derecha está definido por
<pre lang="haskell">
   HasRightInverse (f : α → β) : Prop :=
      ∃ g : β → α, RightInverse g f
</pre>
Finalmente, que \\(f\\) es suprayectiva está definido por
<pre lang="haskell">
   def Surjective (f : α → β) : Prop :=
      ∀ b, ∃ a, f a = b
</pre>

Demostrar con Lean4 que si la función \\(f\\) tiene inversa por la derecha, entonces \\(f\\) es suprayectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {α β: Type _}
variable {f : α → β}

example
  (hf : HasRightInverse f)
  : Surjective f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(f: A → B\\) y \\(g: B → A\\) una inversa por la derecha de \\(f\\). Entonces,
\\[ (∀y ∈ B)[f(g(y)) = y] \\tag{1} \\]

Para demostrar que \\(f\\) es subprayectiva, sea \\(b ∈ B\\). Entonces, \\(g(b) ∈ A\\) y, por (1),
\\[ f(g(b) = b \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {α β: Type _}
variable {f : α → β}

-- 1ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
by
  unfold Surjective
  -- ⊢ ∀ (b : β), ∃ a, f a = b
  unfold HasRightInverse at hf
  -- hf : ∃ finv, Function.RightInverse finv f
  cases' hf with g hg
  -- g : β → α
  -- hg : Function.RightInverse g f
  intro b
  -- b : β
  -- ⊢ ∃ a, f a = b
  use g b
  -- ⊢ f (g b) = b
  exact hg b

-- 2ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
by
  intro b
  -- b : β
  -- ⊢ ∃ a, f a = b
  cases' hf with g hg
  -- g : β → α
  -- hg : Function.RightInverse g f
  use g b
  -- ⊢ f (g b) = b
  exact hg b

-- 3ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
by
  intro b
  -- b : β
  -- ⊢ ∃ a, f a = b
  cases' hf with g hg
  -- g : β → α
  -- hg : Function.RightInverse g f
  exact ⟨g b, hg b⟩

-- 4ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
HasRightInverse.surjective hf

-- Lemas usados
-- ============

-- #check (HasRightInverse.surjective : HasRightInverse f → Surjective f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_funciones_con_inversa_por_la_derecha_son_suprayectivas
imports Main
begin

definition tiene_inversa_dcha :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_dcha f ⟷ (∃g. ∀y. f (g y) = y)"

(* 1ª demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "∀y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then have "f (g y) = y"
    by (rule allE)
  then have "y = f (g y)"
    by (rule sym)
  then show "∃x. y = f x"
    by (rule exI)
qed

(* 2ª demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "∀y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then have "y = f (g y)"
    by simp
  then show "∃x. y = f x"
    by (rule exI)
qed

(* 3ª demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "∀y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then show "∃x. y = f x"
    by metis
qed

(* 4ª demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  show "∃x. y = f x"
    using assms tiene_inversa_dcha_def
    by metis
qed

(* 5ª demostración *)

lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
using assms tiene_inversa_dcha_def surj_def
by metis

end
</pre>
