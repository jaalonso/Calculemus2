---
title: Las familias de conjuntos definen relaciones simétricas
date: 2024-07-05 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Cada familia de conjuntos \\(P\\) define una relación de forma que dos elementos están relacionados si algún conjunto de \\(P\\) contiene a ambos elementos. Se puede definir en Lean4 por
<pre lang="lean">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Demostrar con Lean4 que si \\(P\\) es una familia de subconjuntos de \\(X\\), entonces la relación definida por \\(P\\) es simétrica.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable (P : Set (Set X))

def relacion (P : Set (Set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

example : Symmetric (relacion P) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(x, y ∈ X\\) tales que \\(x\\) está relacionado con \\(y\\) mediante la relación definida por \\(P\\). Entonces, existe \\(A\\) tal que
\\[ A ∈ P ∧ x ∈ A ∧ y ∈ A \\]
Por tanto,
\\[ A ∈ P ∧ y ∈ A ∧ x ∈ A \\]
es decir, \\(y\\) está relacionado con \\(x\\) mediante la relación definida por \\(P\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable (P : Set (Set X))

def relacion (P : Set (Set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

-- 1ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  rcases hxy with ⟨A, h1⟩
  -- A : Set X
  -- h1 : A ∈ P ∧ x ∈ A ∧ y ∈ A
  have h2 : A ∈ P ∧ y ∈ A ∧ x ∈ A := by tauto
  exact ⟨A, h2⟩

-- 2ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  unfold Symmetric
  -- ⊢ ∀ ⦃x y : X⦄, relacion P x y → relacion P y x
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  unfold relacion at *
  -- hxy : ∃ A, A ∈ P ∧ x ∈ A ∧ y ∈ A
  -- ⊢ ∃ A, A ∈ P ∧ y ∈ A ∧ x ∈ A
  rcases hxy with ⟨A, hAP, ⟨hxA, hyA⟩⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  -- hyA : y ∈ A
  use A
  -- ⊢ A ∈ P ∧ y ∈ A ∧ x ∈ A
  repeat' constructor
  . -- ⊢ A ∈ P
    exact hAP
  . -- ⊢ y ∈ A
    exact hyA
  . -- ⊢ x ∈ A
    exact hxA

-- 3ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  rcases hxy with ⟨A, hAP, ⟨hxA, hyA⟩⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  -- hyA : y ∈ A
  use A
  -- ⊢ A ∈ P ∧ y ∈ A ∧ x ∈ A
  (repeat' constructor) <;> assumption

-- 4ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  rcases hxy with ⟨A, hAP, ⟨hxA, hyA⟩⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  -- hyA : y ∈ A
  exact ⟨A, ⟨hAP, hyA, hxA⟩⟩
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_familias_de_conjuntos_definen_relaciones_simetricas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_familias_de_conjuntos_definen_relaciones_simetricas
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

(* 1ª demostración *)

lemma "symp (relacion P)"
proof (rule sympI)
  fix x y
  assume "relacion P x y"
  then have "∃A∈P. x ∈ A ∧ y ∈ A"
    by (unfold relacion_def)
  then have "∃A∈P. y ∈ A ∧ x ∈ A"
  proof (rule bexE)
    fix A
    assume hA1 : "A ∈ P" and hA2 : "x ∈ A ∧ y ∈ A"
    have "y ∈ A ∧ x ∈ A"
      using hA2 by (simp only: conj_commute)
    then show "∃A∈P. y ∈ A ∧ x ∈ A"
      using hA1 by (rule bexI)
  qed
  then show "relacion P y x"
    by (unfold relacion_def)
qed

(* 2ª demostración *)

lemma "symp (relacion P)"
proof (rule sympI)
  fix x y
  assume "relacion P x y"
  then obtain A where "A ∈ P ∧ x ∈ A ∧ y ∈ A"
    using relacion_def
    by metis
  then show "relacion P y x"
    using relacion_def
    by metis
qed

(* 3ª demostración *)

lemma "symp (relacion P)"
  using relacion_def
  by (metis sympI)

end
</pre>
