---
title: Las particiones definen relaciones reflexivas
date: 2024-07-04 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Cada familia de conjuntos \\(P\\) define una relación de forma que dos elementos están relacionados si algún conjunto de \\(P\\) contiene a ambos elementos. Se puede definir en Lean por
<pre lang="lean">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Una familia de subconjuntos de \\(X\\) es una partición de \\(X\\) si cada elemento de \\(X\\) pertenece a un único conjunto de \\(P\\) y todos los elementos de \\(P\\) son no vacíos. Se puede definir en Lean por
<pre lang="lean">
   def particion (P : set (set X)) : Prop :=
     (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
</pre>

Demostrar con Lean4 que si \\(P\\) es una partición de \\(X\\), entonces la relación definida por \\(P\\) es reflexiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable (P : Set (Set X))

def relacion (P : Set (Set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

def particion (P : Set (Set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

example
  (h : particion P)
  : Reflexive (relacion P) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ X\\). Puesto que \\(P\\) es una partición de \\(X\\), existe un \\(A ∈ P\\) tal que \\(x ∈ A\\). Por tanto, se tiene que
\\[ (∃ A ∈ P) [x ∈ A ∧ x ∈ A] \\]
Luego, \\(x\\) está relacionado con \\(x\\) mediante la relación definida por \\(P\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable (P : Set (Set X))

def relacion (P : Set (Set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

def particion (P : Set (Set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

-- 1ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  intro x
  -- x : X
  -- ⊢ relacion P x x
  rcases h.1 x with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  exact ⟨A, hAP, hxA, hxA⟩

-- 2ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  unfold Reflexive
  -- ⊢ ∀ (x : X), relacion P x x
  intro x
  -- x : X
  -- ⊢ relacion P x x
  unfold relacion
  -- ⊢ ∃ A, A ∈ P ∧ x ∈ A ∧ x ∈ A
  unfold particion at h
  -- h : (∀ x, ∃ B, B ∈ P ∧ x ∈ B ∧ ∀ C, C ∈ P → x ∈ C → B = C) ∧ ¬∅ ∈ P
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x
  rcases h with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  use A
  -- ⊢ A ∈ P ∧ x ∈ A ∧ x ∈ A
  repeat' constructor
  . -- ⊢ A ∈ P
    exact hAP
  . -- ⊢ x ∈ A
    exact hxA
  . -- ⊢ x ∈ A
    exact hxA

-- 3ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  intro x
  -- ⊢ relacion P x x
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x
  rcases h with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  use A
  -- ⊢ A ∈ P ∧ x ∈ A ∧ x ∈ A
  repeat' constructor
  . -- ⊢ A ∈ P
    assumption
  . -- ⊢ x ∈ A
    assumption
  . -- ⊢ x ∈ A
    assumption

-- 4ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  intro x
  -- x : X
  -- ⊢ relacion P x x
  rcases (h.1 x) with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  use A
  -- ⊢ A ∈ P ∧ x ∈ A ∧ x ∈ A
  repeat' constructor
  . -- ⊢ A ∈ P
    assumption
  . -- ⊢ x ∈ A
    assumption
  . -- ⊢ x ∈ A
    assumption
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_particiones_definen_relaciones_reflexivas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_particiones_definen_relaciones_reflexivas
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

(* 1ª demostración *)

lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
proof (rule reflpI)
  fix x
  have "(∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"
    using assms by (unfold particion_def)
  then have "∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))"
    by (rule conjunct1)
  then have "∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C)"
    by (rule allE)
  then obtain B where "B ∈ P ∧ (x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))"
    by (rule someI2_bex)
  then obtain B where "(B ∈ P ∧ x ∈ B) ∧ (∀C∈P. x ∈ C ⟶ B = C)"
    by (simp only: conj_assoc)
  then have "B ∈ P ∧ x ∈ B"
    by (rule conjunct1)
  then have "x ∈ B"
    by (rule conjunct2)
  then have "x ∈ B ∧ x ∈ B"
    using ‹x ∈ B› by (rule conjI)
  moreover have "B ∈ P"
    using ‹B ∈ P ∧ x ∈ B› by (rule conjunct1)
  ultimately have "∃B∈P. x ∈ B ∧ x ∈ B"
    by (rule bexI)
  then show "relacion P x x"
    by (unfold relacion_def)
qed

(* 2ª demostración *)

lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
proof (rule reflpI)
  fix x
  obtain A where "A ∈ P ∧ x ∈ A"
    using assms particion_def
    by metis
  then show "relacion P x x"
    using relacion_def
    by metis
qed

(* 3ª demostración *)

lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
  using assms particion_def relacion_def
  by (metis reflp_def)

end
</pre>
