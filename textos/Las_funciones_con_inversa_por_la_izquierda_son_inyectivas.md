---
title: Las funciones con inversa por la izquierda son inyectivas
date: 2024-06-05 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

En Lean4, que \\(g\\) es una inversa por la izquierda de \\(f\\) está definido por
<pre lang="lean">
   LeftInverse (g : β → α) (f : α → β) : Prop :=
      ∀ x, g (f x) = x
</pre>
y que \\(f\\) tenga inversa por la izquierda está definido por
<pre lang="lean">
   HasLeftInverse (f : α → β) : Prop :=
      ∃ finv : β → α, LeftInverse finv f
</pre>
Finalmente, que \\(f\\) es inyectiva está definido por
<pre lang="lean">
   Injective (f : α → β) : Prop :=
      ∀ ⦃x y⦄, f x = f y → x = y
</pre>

Demostrar con Lean4 que si \\(f\\) tiene inversa por la izquierda, entonces \\(f\\) es inyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

universe u v
variable {α : Type u}
variable {β : Type v}
variable {f : α → β}

example
  (hf : HasLeftInverse f)
  : Injective f :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(f: A → B\\) que tiene inversa por la izquierda. Entonces, existe una \\(g: B → A) tal que
\\[ (∀ x ∈ A)[g(f(x)) = x] \\tag{1} \\]
Para demostrar que \\(f\\) es inyectiva, sean \\(x, y ∈ A\\) tales que
\\[ f(x) = f(y) \\]
Entonces,
\\[ g(f(x)) = g(f(y)) \\]
y, por (1),
\\[ x = y \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

universe u v
variable {α : Type u}
variable {β : Type v}
variable {f : α → β}

-- 1ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
by
  intros x y hxy
  -- x y : α
  -- hxy : f x = f y
  -- ⊢ x = y
  unfold HasLeftInverse at hf
  -- hf : ∃ finv, LeftInverse finv f
  unfold LeftInverse at hf
  -- hf : ∃ finv, ∀ (x : α), finv (f x) = x
  cases' hf with g hg
  -- g : β → α
  -- hg :
  calc x = g (f x) := (hg x).symm
       _ = g (f y) := congr_arg g hxy
       _ = y       := hg y

-- 2ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
by
  intros x y hxy
  -- x y : α
  -- hxy : f x = f y
  -- ⊢ x = y
  cases' hf with g hg
  -- g : β → α
  -- hg : LeftInverse g f
  calc x = g (f x) := (hg x).symm
       _ = g (f y) := congr_arg g hxy
       _ = y       := hg y

-- 3ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
by
  apply Exists.elim hf
  -- ⊢ ∀ (a : β → α), LeftInverse a f → Injective f
  intro g hg
  -- g : β → α
  -- hg : LeftInverse g f
  -- ⊢ Injective f
  exact LeftInverse.injective hg

-- 4ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
Exists.elim hf (fun _g hg ↦ LeftInverse.injective hg)

-- 5ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
HasLeftInverse.injective hf

-- Lemas usados
-- ============

-- variable (x y : α)
-- variable (p : α → Prop)
-- variable (b : Prop)
-- variable (g : β → α)
-- #check (Exists.elim : (∃ x, p x) → (∀ x, p x → b) → b)
-- #check (LeftInverse.injective : LeftInverse g f → Injective f)
-- #check (congr_arg f : x = y → f x = f y)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_funciones_con_inversa_por_la_izquierda_son_inyectivas
imports Main
begin

definition tiene_inversa_izq :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_izq f ⟷ (∃g. ∀x. g (f x) = x)"

(* 1ª demostración *)

lemma
  assumes "tiene_inversa_izq f"
  shows   "inj f"
proof (unfold inj_def; intro allI impI)
  fix x y
  assume "f x = f y"
  obtain g where hg : "∀x. g (f x) = x"
    using assms tiene_inversa_izq_def by auto
  have "x = g (f x)"
    by (simp only: hg)
  also have "… = g (f y)"
    by (simp only: ‹f x = f y›)
  also have "… = y"
    by (simp only: hg)
  finally show "x = y" .
qed

(* 2ª demostración *)

lemma
  assumes "tiene_inversa_izq f"
  shows   "inj f"
  by (metis assms inj_def tiene_inversa_izq_def)

end
</pre>
