---
title: La composición de una función creciente y una decreciente es decreciente
date: 2024-05-21 06:00:00 UTC+02:00
category: Funciones_reales
has_math: true
---

[mathjax]

Sea una función \\(f\\) de \\(ℝ\\) en \\(ℝ\\). Se dice que \\(f\\) es **creciente** si para todo \\(x\\) e \\(y\\) tales que \\(x ≤ y\\) se tiene que \\(f(x) ≤ f(y)\\). Se dice que \\(f\\) es **decreciente** si para todo \\(x\\) e \\(y\\) tales que \\(x ≤ y\\) se tiene que \\(f(x) ≥ f(y)\\).

Demostrar con Lean4 que si \\(f\\) es creciente y \\(g\\) es decreciente, entonces \\(g ∘ f\\) es decreciente.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

def creciente (f : ℝ → ℝ) : Prop :=
  ∀ {x y}, x ≤ y → f x ≤ f y

def decreciente (f : ℝ → ℝ) : Prop :=
  ∀ {x y}, x ≤ y → f x ≥ f y

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(x, y ∈ ℝ\\) tales que \\(x ≤ y\\). Entonces, por ser \\(f\\) creciente,
\\[ f(x) ≥ f(y) \\]
y, por ser g decreciente,
\\[ g(f(x)) ≤ g(f(y)) \\]
Por tanto,
\\[ (g ∘ f)(x) ≤ (g ∘ f)(y) \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

def creciente (f : ℝ → ℝ) : Prop :=
  ∀ {x y}, x ≤ y → f x ≤ f y

def decreciente (f : ℝ → ℝ) : Prop :=
  ∀ {x y}, x ≤ y → f x ≥ f y

-- 1ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intro x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  have h1 : f x ≤ f y := hf h
  show (g ∘ f) x ≥ (g ∘ f) y
  exact hg h1

-- 2ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intro x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  show (g ∘ f) x ≥ (g ∘ f) y
  exact hg (hf h)

-- 3ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
fun {_ _} h ↦ hg (hf h)

-- 4ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y hxy
  calc (g ∘ f) x
       = g (f x)   := rfl
     _ ≥ g (f y)   := hg (hf hxy)
     _ = (g ∘ f) y := rfl

-- 5ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  unfold creciente decreciente at *
  -- hf : ∀ {x y : ℝ}, x ≤ y → f x ≤ f y
  -- hg : ∀ {x y : ℝ}, x ≤ y → g x ≥ g y
  -- ⊢ ∀ {x y : ℝ}, x ≤ y → (g ∘ f) x ≥ (g ∘ f) y
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  unfold Function.comp
  -- ⊢ g (f x) ≥ g (f y)
  apply hg
  -- ⊢ f x ≤ f y
  apply hf
  -- ⊢ x ≤ y
  exact h

-- 6ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  apply hg
  -- ⊢ f x ≤ f y
  apply hf
  -- ⊢ x ≤ y
  exact h

-- 7ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  apply hg
  -- ⊢ f x ≤ f y
  exact hf h

-- 8ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  exact hg (hf h)

-- 9ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by tauto
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente
imports Main HOL.Real
begin

(* 1ª demostración *)

lemma
  fixes f g :: "real ⇒ real"
  assumes "mono f"
          "antimono g"
  shows   "antimono (g ∘ f)"
proof (rule antimonoI)
  fix x y :: real
  assume "x ≤ y"
  have "(g ∘ f) y = g (f y)"
    by (simp only: o_apply)
  also have "… ≤ g (f x)"
    using assms ‹x ≤ y›
    by (metis antimonoE monoD)
  also have "… = (g ∘ f) x"
    by (simp only: o_apply)
  finally show "(g ∘ f) x ≥ (g ∘ f) y"
    by this
qed

(* 2ª demostración *)

lemma
  fixes f g :: "real ⇒ real"
  assumes "mono f"
          "antimono g"
  shows   "antimono (g ∘ f)"
proof (rule antimonoI)
  fix x y :: real
  assume "x ≤ y"
  have "(g ∘ f) y = g (f y)"    by simp
  also have "… ≤ g (f x)"     by (meson ‹x ≤ y› assms antimonoE monoE)
  also have "… = (g ∘ f) x"    by simp
  finally show "(g ∘ f) x ≥ (g ∘ f) y" .
qed

(* 3ª demostración *)

lemma
  assumes "mono f"
          "antimono g"
  shows   "antimono (g ∘ f)"
  using assms(1) assms(2) monotone_on_o
  by blast

end
</pre>
