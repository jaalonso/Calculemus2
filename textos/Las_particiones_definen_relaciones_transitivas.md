---
title: Las particiones definen relaciones transitivas
date: 2024-07-08 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Cada familia de conjuntos \\(P\\) define una relación de forma que dos elementos están relacionados si algún conjunto de \\(P\\) contiene a ambos elementos. Se puede definir en Lean4 por
<pre lang="lean">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Una familia \\(P\\) de subconjuntos de \\(X\\) es una partición de \\(X\\) si cada elemento de \\(X\\) pertenece a un único conjunto de \\(P\\) y todos los elementos de \\(P\\) son no vacíos. Se puede definir en Lean por
<pre lang="lean">
   def particion (P : set (set X)) : Prop :=
     (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
</pre>

Demostrar con Lean4 que si \\(P\\) es una partición de \\(X\\), entonces la relación definida por \\(P\\) es transitiva.

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
  : Transitive (relacion P) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(R\\) la relación definida por \\(P\\) y \\(x, y, z ∈ X\\) tales que \\(xRy\\) e \\(yRz\\). Entonces, existen \\(B₁\\) y \\(B₂\\) tales que
\\begin{align}
   &B₁ ∈ P ∧ x ∈ B₁ ∧ y ∈ B₁  \\tag{1} \\\\
   &B₂ ∈ P ∧ y ∈ B₂ ∧ z ∈ B₂  \\tag{2}
\\end{align}
Si demostramos que \\(B₁ = B₂\\), se tiene que
\\[ B₁ ∈ P ∧ x ∈ B₁ ∧ z ∈ B₁ \\]
y, por tanto, \\(xRz\\).

Para demostrar que \\(B₁ = B_2\\), se observa que, por ser \\(P\\) una partición
de \\(X\\), se tiene
\\[ (∀ x ∈ X)(∃ B ∈ P)(∀ C ∈ P)[x ∈ C → B = C] \\]
por tanto, existe un \\(B ∈ P\\) tal que
\\[ (∀ C ∈ P)[y ∈ C → B = C] \\tag{3} \\]
Entonces, de (3) y (1), se tiene
\\begin{align}
   B₁ &= B     &&\\text{[de (3) y (1)]} \\\\
      &= B₂    &&\\text{[de (3) y (2)]}
\\end{align}

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
  : Transitive (relacion P) :=
by
  rintro x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩
  -- x y z : X
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  -- ⊢ relacion P x z
  have h1 : B1 = B2 := by
    rcases (h.1 y) with ⟨B, -, -, hB⟩
    -- B : Set X
    -- hB : ∀ (C : Set X), C ∈ P → y ∈ C → B = C
    calc B1 = B  := by exact (hB B1 hB1P hyB1).symm
          _ = B2 := hB B2 hB2P hyB2
  repeat' constructor
  . -- ⊢ B1 ∈ P
    exact hB1P
  . -- ⊢ x ∈ B1
    exact hxB1
  . -- ⊢ z ∈ B1
    rw [h1]
    -- ⊢ z ∈ B2
    exact hzB2

-- 2ª demostración
-- ===============

example
  (h : particion P)
  : Transitive (relacion P) :=
by
  unfold Transitive
  -- ⊢ ∀ ⦃x y z : X⦄, relacion P x y → relacion P y z → relacion P x z
  intros x y z h1 h2
  -- x y z : X
  -- h1 : relacion P x y
  -- h2 : relacion P y z
  -- ⊢ relacion P x z
  unfold relacion at *
  -- h1 : ∃ A, A ∈ P ∧ x ∈ A ∧ y ∈ A
  -- h2 : ∃ A, A ∈ P ∧ y ∈ A ∧ z ∈ A
  -- ⊢ ∃ A, A ∈ P ∧ x ∈ A ∧ z ∈ A
  rcases h1 with ⟨B1, hB1P, hxB1, hyB1⟩
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  rcases h2 with ⟨B2, hB2P, hyB2, hzB2⟩
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  use B1
  -- ⊢ B1 ∈ P ∧ x ∈ B1 ∧ z ∈ B1
  repeat' constructor
  . -- ⊢ B1 ∈ P
    exact hB1P
  . -- ⊢ x ∈ B1
    exact hxB1
  . -- ⊢ z ∈ B1
    convert hzB2
    -- ⊢ B1 = B2
    rcases (h.1 y) with ⟨B, -, -, hB⟩
    -- B : Set X
    -- hB : ∀ (C : Set X), C ∈ P → y ∈ C → B = C
    have hBB1 : B = B1 := hB B1 hB1P hyB1
    have hBB2 : B = B2 := hB B2 hB2P hyB2
    exact Eq.trans hBB1.symm hBB2

-- 3ª demostración
-- ===============

example
  (h : particion P)
  : Transitive (relacion P) :=
by
  rintro x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩
  -- x y z : X
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  -- ⊢ relacion P x z
  use B1
  -- ⊢ B1 ∈ P ∧ x ∈ B1 ∧ z ∈ B1
  repeat' constructor
  . -- ⊢ B1 ∈ P
    exact hB1P
  . -- ⊢ x ∈ B1
    exact hxB1
  . -- ⊢ z ∈ B1
    convert hzB2
    -- ⊢ B1 = B2
    rcases (h.1 y) with ⟨B, -, -, hB⟩
    -- B : Set X
    -- hB : ∀ (C : Set X), C ∈ P → y ∈ C → B = C
    exact Eq.trans (hB B1 hB1P hyB1).symm (hB B2 hB2P hyB2)

-- 4ª demostración
-- ===============

example
  (h : particion P)
  : Transitive (relacion P) :=
by
  rintro x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩
  -- x y z : X
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  -- ⊢ relacion P x z
  exact ⟨B1, ⟨hB1P,
              hxB1,
              by { convert hzB2
                   rcases (h.1 y) with ⟨B, -, -, hB⟩
                   exact Eq.trans (hB B1 hB1P hyB1).symm
                                  (hB B2 hB2P hyB2) }⟩⟩

-- Lemas usados
-- ============

-- variable (x y z : X)
-- #check (Eq.trans : x = y → y = z → x = z)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_particiones_definen_relaciones_transitivas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_particiones_definen_relaciones_transitivas
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

(* 1ª demostración *)

lemma
  assumes "particion P"
  shows   "transp (relacion P)"
proof (rule transpI)
  fix x y z
  assume "relacion P x y" and "relacion P y z"
  have "∃A∈P. x ∈ A ∧ y ∈ A"
    using ‹relacion P x y›
    by (simp only: relacion_def)
  then obtain A where "A ∈ P" and hA : "x ∈ A ∧ y ∈ A"
    by (rule bexE)
  have "∃B∈P. y ∈ B ∧ z ∈ B"
    using ‹relacion P y z›
    by (simp only: relacion_def)
  then obtain B where "B ∈ P" and hB : "y ∈ B ∧ z ∈ B"
    by (rule bexE)
  have "A = B"
  proof -
    have "∃C ∈ P. y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
      using assms
      by (simp only: particion_def)
    then obtain C where "C ∈ P"
                    and hC : "y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
      by (rule bexE)
    have hC' : "∀D∈P. y ∈ D ⟶ C = D"
      using hC by (rule conjunct2)
    have "C = A"
      using ‹A ∈ P› hA hC' by simp
    moreover have "C = B"
      using ‹B ∈ P› hB hC by simp
    ultimately show "A = B"
      by (rule subst)
  qed
  then have "x ∈ A ∧ z ∈ A"
    using hA hB by simp
  then have "∃A∈P. x ∈ A ∧ z ∈ A"
    using ‹A ∈ P› by (rule bexI)
  then show "relacion P x z"
    using ‹A = B› ‹A ∈ P›
    by (unfold relacion_def)
qed

(* 2ª demostración *)

lemma
  assumes "particion P"
  shows   "transp (relacion P)"
proof (rule transpI)
  fix x y z
  assume "relacion P x y" and "relacion P y z"
  obtain A where "A ∈ P" and hA : "x ∈ A ∧ y ∈ A"
    using ‹relacion P x y›
    by (meson relacion_def)
  obtain B where "B ∈ P" and hB : "y ∈ B ∧ z ∈ B"
    using ‹relacion P y z›
    by (meson relacion_def)
  have "A = B"
  proof -
    obtain C where "C ∈ P" and hC : "y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
      using assms particion_def
      by metis
    have "C = A"
      using ‹A ∈ P› hA hC by auto
    moreover have "C = B"
      using ‹B ∈ P› hB hC by auto
    ultimately show "A = B"
      by simp
  qed
  then have "x ∈ A ∧ z ∈ A"
    using hA hB by auto
  then show "relacion P x z"
    using ‹A = B› ‹A ∈ P› relacion_def
    by metis
qed

(* 3ª demostración *)

lemma
  assumes "particion P"
  shows   "transp (relacion P)"
  using assms particion_def relacion_def
  by (smt (verit) transpI)

end
</pre>
