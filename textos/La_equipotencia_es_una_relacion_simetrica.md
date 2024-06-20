---
title: La equipotencia es una relación simétrica
date: 2024-06-20 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Dos conjuntos \\(A\\) y \\(B\\) son equipotentes (y se denota por \\(A ≃ B\\)) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean4 por
<pre lang="lean4">
   def es_equipotente (A B : Type _) : Prop :=
     ∃ g : A → B, Bijective g

   local infixr:50 " ⋍ " => es_equipotente
</pre>

Demostrar con Lean4 que la relación de equipotencia es simétrica.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

open Function

def es_equipotente (A B : Type _) : Prop :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

lemma aux1
  (hf : Bijective f)
  : tiene_inversa f :=
by
  cases' (bijective_iff_has_inverse.mp hf) with g hg
  -- g : Y → X
  -- hg : LeftInverse g f ∧ Function.RightInverse g f
  aesop (add norm unfold [tiene_inversa, inversa])

lemma aux2
  (hg : inversa g f)
  : Bijective g :=
by
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

example : Symmetric (. ⋍ .) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(A\\) y \\(B\\) tales que \\(A ⋍ B\\). Entonces, existe \\(f: A → B\\) biyectiva. Por tanto, f tiene una inversa \\(g: B → A\\) que también es biyectiva. Luego, \\(B ⋍ A\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

open Function

def es_equipotente (A B : Type _) : Prop :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

lemma aux1
  (hf : Bijective f)
  : tiene_inversa f :=
by
  cases' (bijective_iff_has_inverse.mp hf) with g hg
  -- g : Y → X
  -- hg : LeftInverse g f ∧ Function.RightInverse g f
  aesop (add norm unfold [tiene_inversa, inversa])

lemma aux2
  (hg : inversa g f)
  : Bijective g :=
by
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

-- 1ª demostración
-- ===============

example : Symmetric (. ⋍ .) :=
by
  unfold Symmetric
  -- ⊢ ∀ ⦃x y : Type ?u.17753⦄, (fun x x_1 => x ⋍ x_1) x y → (fun x x_1 => x ⋍ x_1) y x
  intros x y hxy
  -- x y : Type ?u.17753
  -- hxy : x ⋍ y
  -- ⊢ y ⋍ x
  unfold es_equipotente at *
  -- hxy : ∃ g, Bijective g
  -- ⊢ ∃ g, Bijective g
  cases' hxy with f hf
  -- f : x → y
  -- hf : Bijective f
  have h1 : tiene_inversa f := aux1 hf
  cases' h1 with g hg
  -- g : y → x
  -- hg : inversa g f
  use g
  -- ⊢ Bijective g
  exact aux2 hg

-- 2ª demostración
-- ===============

example : Symmetric (. ⋍ .) :=
by
  intros x y hxy
  -- x y : Type ?u.17965
  -- hxy : x ⋍ y
  -- ⊢ y ⋍ x
  cases' hxy with f hf
  -- f : x → y
  -- hf : Bijective f
  cases' (aux1 hf) with g hg
  -- g : y → x
  -- hg : inversa g f
  exact ⟨g, aux2 hg⟩

-- 3ª demostración
-- ===============

example : Symmetric (. ⋍ .) :=
by
  rintro x y ⟨f, hf⟩
  -- x y : Type ?u.18159
  -- f : x → y
  -- hf : Bijective f
  -- ⊢ y ⋍ x
  cases' (aux1 hf) with g hg
  -- g : y → x
  -- hg : inversa g f
  exact ⟨g, aux2 hg⟩

-- Lemas usados
-- ============

-- variable (α β : Type _)
-- variable (f : α → β)
-- #check (bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_equipotencia_es_una_relacion_simetrica.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_equipotencia_es_una_relacion_simetrica
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)

lemma "symp (≈)"
proof (rule sympI)
  fix x y :: "'a set"
  assume "x ≈ y"
  then obtain f where "bij_betw f x y"
    using eqpoll_def by blast
  then have "bij_betw (the_inv_into x f) y x"
    by (rule bij_betw_the_inv_into)
  then have "∃g. bij_betw g y x"
    by auto
  then show "y ≈ x"
    by (simp only: eqpoll_def)
qed

(* 2ª demostración *)

lemma "symp (≈)"
  unfolding eqpoll_def symp_def
  using bij_betw_the_inv_into by auto

(* 3ª demostración *)

lemma "symp (≈)"
  by (simp add: eqpoll_sym sympI)

end
</pre>
