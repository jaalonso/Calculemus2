---
title: La equipotencia es una relación de equivalencia
date: 2024-06-25 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Dos conjuntos \(A\) y \(B\) son equipotentes (y se denota por \(A ≃ B\)) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean4 por
<pre lang="lean">
   def es_equipotente (A B : Type _) : Prop :=
     ∃ g : A → B, Bijective g

   local infixr:50 " ⋍ " => es_equipotente
</pre>

Demostrar con Lean4 que la relación de equipotencia es simétrica.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

def es_equipotente (A B : Type _) :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

variable {X Y : Type _}
variable {f : X → Y}
variable {g : Y → X}

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
  apply bijective_iff_has_inverse.mpr
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

example : Equivalence (. ⋍ .) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que la equipotencia es reflexiva, simétrica y
transitiva. Para ello, usaremos los siguientes lemas demostrados en
ejercicios anteriores:

+ Lema 1: Si \(f\) es biyectiva, entonces tiene inversa.
+ Lema 2: Si \(g\) es la inversa de \(f\), entonces \(g\) es biyectiva.

Para demostrar que \(⋍\) es reflexiva, sea \(X\) un conjunto. Entonces, la identidad es una biyección de \(X\) en \(X\). Por tanto, \(X ⋍ X\).

Para demostrar que \(⋍\) es simétrica, sean \(X\), \(Y\) tales que \(X ⋍  Entonces, existe \(f: X → Y\) biyectiva. Por el Lema 1, existe una \(g: X → Y\) que es la inversa de \(f\). Por el lema 2, \(g\) es biyectiva y, por tanto, \(Y ⋍ X).

Para demostrar que \(⋍\) es transitiva, sean \(X\), \(Y\), \(Z\) tales que \(X ⋍ Y\) y \(Y ⋍ Z\). Entonces, existen \(f: X → Y\) y \(g: Y → Z\) biyectivas. Luego, \(g ∘ f: X → Z\) es biyectiva y, por tanto, \(X ⋍ Z\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

def es_equipotente (A B : Type _) :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

variable {X Y : Type _}
variable {f : X → Y}
variable {g : Y → X}

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
  apply bijective_iff_has_inverse.mpr
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

example : Equivalence (. ⋍ .) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : Type ?u.20188), x ⋍ x
    exact fun X ↦ ⟨id, bijective_id⟩
  . -- ⊢ ∀ {x y : Type ?u.20188}, x ⋍ y → y ⋍ x
    rintro X Y ⟨f, hf⟩
    -- X Y : Type ?u.20188
    -- f : X → Y
    -- hf : Bijective f
    -- ⊢ Y ⋍ X
    cases' (aux1 hf) with g hg
    -- g : Y → X
    -- hg : inversa g f
    exact ⟨g, aux2 hg⟩
  . -- ⊢ ∀ {x y z : Type ?u.20188}, x ⋍ y → y ⋍ z → x ⋍ z
    rintro X Y Z ⟨f, hf⟩ ⟨g, hg⟩
    -- X Y Z : Type ?u.20188
    -- f : X → Y
    -- hf : Bijective f
    -- g : Y → Z
    -- hg : Bijective g
    -- ⊢ X ⋍ Z
    exact ⟨g ∘ f, Bijective.comp hg hf⟩

-- Lemas usados
-- ============

-- #check (Bijective.comp : Bijective g → Bijective f → Bijective (g ∘ f))
-- #check (bijective_id : Bijective id)
-- #check (bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_equipotencia_es_una_relacion_de_equivalencia.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_equipotencia_es_una_relacion_de_equivalencia
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)

lemma "equivp (≈)"
proof (rule equivpI)
  show "reflp (≈)"
    using reflpI eqpoll_refl by blast
next
  show "symp (≈)"
    using sympI eqpoll_sym by blast
next
  show "transp (≈)"
    using transpI eqpoll_trans by blast
qed

(* 2ª demostración *)

lemma "equivp (≈)"
  by (simp add: equivp_reflp_symp_transp
                reflpI
                sympI
                eqpoll_sym
                transpI
                eqpoll_trans)

end
</pre>
