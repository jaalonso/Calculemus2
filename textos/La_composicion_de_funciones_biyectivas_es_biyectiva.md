---
title: La composición de funciones biyectivas es biyectiva
date: 2024-06-21 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Demostrar con Lean4 que la composición de dos funciones biyectivas es una función biyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \(f: X → Y\) y \(g: Y → Z\). En ejercicios anteriores hemos demostrados
los siguientes lemas:

+ Lema 1: Si \(f\) y \(g\) son inyectiva, entonces también lo es \(g ∘ f\).
+ Lema 2: Si \(f\) y \(g\) son suprayectiva, entonces también lo es \(g ∘ f\).

Supongamos que \(f\) y \(g\) son biyectivas. Entonces, son inyectivas y suprayectivas. Luego, por los lemas 1 y 2, \(g ∘ f\) es inyectiva y suprayectiva. Por tanto, \(g ∘ f\) es biyectiva.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by
  cases' Hf with Hfi Hfs
  -- Hfi : Injective f
  -- Hfs : Surjective f
  cases' Hg with Hgi Hgs
  -- Hgi : Injective g
  -- Hgs : Surjective g
  constructor
  . -- ⊢ Injective (g ∘ f)
    apply Injective.comp
    . -- ⊢ Injective g
      exact Hgi
    . -- ⊢ Injective f
      exact Hfi
  . apply Surjective.comp
    . -- ⊢ Surjective g
      exact Hgs
    . -- ⊢ Surjective f
      exact Hfs

-- 2ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by
  cases' Hf with Hfi Hfs
  -- Hfi : Injective f
  -- Hfs : Surjective f
  cases' Hg with Hgi Hgs
  -- Hgi : Injective g
  -- Hgs : Surjective g
  constructor
  . -- ⊢ Injective (g ∘ f)
    exact Injective.comp Hgi Hfi
  . -- ⊢ Surjective (g ∘ f)
    exact Surjective.comp Hgs Hfs

-- 3ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by
  cases' Hf with Hfi Hfs
  -- Hfi : Injective f
  -- Hfs : Surjective f
  cases' Hg with Hgi Hgs
  -- Hgi : Injective g
  -- Hgs : Surjective g
  exact ⟨Injective.comp Hgi Hfi,
         Surjective.comp Hgs Hfs⟩

-- 4ª demostración
-- ===============

example :
  Bijective f → Bijective g → Bijective (g ∘ f) :=
by
  rintro ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩
  -- Hfi : Injective f
  -- Hfs : Surjective f
  -- Hgi : Injective g
  -- Hgs : Surjective g
  exact ⟨Injective.comp Hgi Hfi,
         Surjective.comp Hgs Hfs⟩

-- 5ª demostración
-- ===============

example :
  Bijective f → Bijective g → Bijective (g ∘ f) :=
fun ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩ ↦ ⟨Injective.comp Hgi Hfi,
                             Surjective.comp Hgs Hfs⟩

-- 6ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
Bijective.comp Hg Hf

-- Lemas usados
-- ============

-- #check (Bijective.comp : Bijective g → Bijective f → Bijective (g ∘ f))
-- #check (Injective.comp : Injective g → Injective f → Injective (g ∘ f))
-- #check (Surjective.comp : Surjective g → Surjective f → Surjective (g ∘ f))
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_composicion_de_funciones_biyectivas_es_biyectiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_composicion_de_funciones_biyectivas_es_biyectiva
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
proof (rule bijI)
  show "inj (g ∘ f)"
  proof (rule inj_compose)
    show "inj g"
      using ‹bij g› by (rule bij_is_inj)
  next
    show "inj f"
      using ‹bij f› by (rule bij_is_inj)
  qed
next
  show "surj (g ∘ f)"
  proof (rule comp_surj)
    show "surj f"
      using ‹bij f› by (rule bij_is_surj)
  next
    show "surj g"
      using ‹bij g› by (rule bij_is_surj)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
proof (rule bijI)
  show "inj (g ∘ f)"
  proof (rule inj_compose)
    show "inj g"
      by (rule bij_is_inj [OF ‹bij g›])
  next
    show "inj f"
      by (rule bij_is_inj [OF ‹bij f›])
  qed
next
  show "surj (g ∘ f)"
  proof (rule comp_surj)
    show "surj f"
      by (rule bij_is_surj [OF ‹bij f›])
  next
    show "surj g"
      by (rule bij_is_surj [OF ‹bij g›])
  qed
qed

(* 3ª demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
proof (rule bijI)
  show "inj (g ∘ f)"
    by (rule inj_compose [OF bij_is_inj [OF ‹bij g›]
                             bij_is_inj [OF ‹bij f›]])
next
  show "surj (g ∘ f)"
    by (rule comp_surj [OF bij_is_surj [OF ‹bij f›]
                           bij_is_surj [OF ‹bij g›]])
qed

(* 4ª demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
by (rule bijI [OF inj_compose [OF bij_is_inj  [OF ‹bij g›]
                                  bij_is_inj  [OF ‹bij f›]]
                  comp_surj   [OF bij_is_surj [OF ‹bij f›]
                                  bij_is_surj [OF ‹bij g›]]])

(* 5ª demostración *)

lemma
  assumes "bij f"
          "bij g"
  shows   "bij (g ∘ f)"
using assms
by (rule bij_comp)

(* Nota: Auto solve indica la demostración anterior. *)

end
</pre>
