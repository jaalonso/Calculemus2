---
title: Las particiones definen relaciones de equivalencia
date: 2024-07-09 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Cada familia de conjuntos \\(P\\) define una relación de forma que dos elementos están relacionados si algún conjunto de \\(P\\) contiene a ambos elementos. Se puede definir en Lean4 por
<pre lang="lean">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Una familia \\(P\\) de subconjuntos de \\(X\\) es una partición de \\(X\\) si cada elemento de \\(X\\) pertenece a un único conjunto de \\(P\\) y todos los elementos de \\(P\\) son no vacíos. Se puede definir en Lean4 por
<pre lang="lean">
   def particion (P : set (set X)) : Prop :=
     (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
</pre>

Demostrar con Lean4 que si \\(P\\) es una partición de \\(X\\), entonces la relación definida por \\(P\\) es una relación de equivalencia.

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
  : Equivalence (relacion P) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(R\\) la relación definida por \\(P\\). Tenemos que demostrar que \\(R\\) es reflexiva, simétrica y transitiva.

Para demostrar que \\(R\\) es reflexiva, sea \\(x ∈ X\\). Puesto que \\(P\\) es una partición de \\(X\\), existe un \\(A ∈ P) tal que \\(x ∈ A). Por tanto, se tiene que
\\[ (∃ A ∈ P) [x ∈ A ∧ x ∈ A] \\]
Luego, \\(xRx\\).

Para demostrar que \\(R\\) es simétrica, sean \\(x, y ∈ X\\) tales que \\(xRy\\). Entonces, existe \\(A\\) tal que
\\[ A ∈ P ∧ x ∈ A ∧ y ∈ A \\]
Por tanto,
\\[ A ∈ P ∧ y ∈ A ∧ x ∈ A \\]
es decir, \\(yRx\\).

Para demostrar que \\(R\\) es transitiva, sean \\(x, y, z ∈ X\\) tales que \\(xRy\\) e \\(yRz\\). Entonces, existen \\(B_1\\) y \\(B_2\\) tales que
\\begin{align}
   &B_1 ∈ P ∧ x ∈ B_1 ∧ y ∈ B_1 \\tag{1} \\\\
   &B_2 ∈ P ∧ y ∈ B_2 ∧ z ∈ B_2 \\tag{2}
\\end{align}
Si demostramos que \\(B_1 = B_2\\), se tiene que
\\[ B_1 ∈ P ∧ x ∈ B_1 ∧ z ∈ B_1 \\]
y, por tanto, \\(xRz\\).

Para demostrar que \\(B_1 = B_2\\), se observa que, por ser \\(P\\) una partición de \\(X\\), se tiene
\\[ (∀ x ∈ X)(∃ B ∈ P)(∀ C ∈ P)[x ∈ C → B = C] \\]
por tanto, para \\(y\\), existe un \\(B ∈ P\\) tal que
\\[ (∀ C ∈ P)[y ∈ C → B = C] \\tag{3} \\]
Entonces,
\\begin{align}
   B_1 &= B      &&\\text{[de (3) y (1)]} \\\\
       &= B_2    &&\\text{[de (3) y (2)]}
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

example
  (h : particion P)
  : Equivalence (relacion P) :=
by
  set R := relacion P
  repeat' constructor
  . -- ⊢ ∀ (x : X), R x x
    intro x
    -- x : X
    -- ⊢ R x x
    rcases (h.1 x) with ⟨A, hAP, hxA, -⟩
    -- A : Set X
    -- hAP : A ∈ P
    -- hxA : x ∈ A
    -- ⊢ R x x
    exact ⟨A, ⟨hAP, hxA, hxA⟩⟩
  . -- ⊢ ∀ {x y : X}, R x y → R y x
    intros x y hxy
    -- x y : X
    -- hxy : R x y
    -- ⊢ R y x
    rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩
    -- B : Set X
    -- hBP : B ∈ P
    -- hxB : x ∈ B
    -- hyB : y ∈ B
    exact ⟨B, ⟨hBP, hyB, hxB⟩⟩
  . -- ⊢ ∀ {x y z : X}, R x y → R y z → R x z
    rintro x y z ⟨B1, hB1P, hxB1, hyB1⟩ ⟨B2, hB2P, hyB2, hzB2⟩
    -- x y z : X
    -- B1 : Set X
    -- hB1P : B1 ∈ P
    -- hxB1 : x ∈ B1
    -- hyB1 : y ∈ B1
    -- B2 : Set X
    -- hB2P : B2 ∈ P
    -- hyB2 : y ∈ B2
    -- hzB2 : z ∈ B2
    -- ⊢ R x z
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

-- 2ª demostración
-- ===============

example
  (h : particion P)
  : Equivalence (relacion P) :=
by
  set R := relacion P
  repeat' constructor
  . -- ⊢ ∀ (x : X), R x x
    intro x
    -- x : X
    -- ⊢ R x x
    rcases (h.1 x) with ⟨A, hAP, hxA, -⟩
    -- A : Set X
    -- hAP : A ∈ P
    -- hxA : x ∈ A
    -- ⊢ R x x
    exact ⟨A, ⟨hAP, hxA, hxA⟩⟩
  . -- ⊢ ∀ {x y : X}, R x y → R y x
    intros x y hxy
    -- x y : X
    -- hxy : R x y
    -- ⊢ R y x
    rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩
    -- B : Set X
    -- hBP : B ∈ P
    -- hxB : x ∈ B
    -- hyB : y ∈ B
    exact ⟨B, ⟨hBP, hyB, hxB⟩⟩
  . -- ⊢ ∀ {x y z : X}, R x y → R y z → R x z
    rintro x y z ⟨B1, hB1P, hxB1, hyB1⟩ ⟨B2, hB2P, hyB2, hzB2⟩
    -- x y z : X
    -- B1 : Set X
    -- hB1P : B1 ∈ P
    -- hxB1 : x ∈ B1
    -- hyB1 : y ∈ B1
    -- B2 : Set X
    -- hB2P : B2 ∈ P
    -- hyB2 : y ∈ B2
    -- hzB2 : z ∈ B2
    -- ⊢ R x z
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

-- Lemas usados
-- ============

-- variable (x y z : X)
-- #check (Eq.trans : x = y → y = z → x = z)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_particiones_definen_relaciones_de_equivalencia.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_particiones_definen_relaciones_de_equivalencia
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

(* 1ª demostración *)

lemma
  assumes "particion P"
  shows   "equivp (relacion P)"
proof (rule equivpI)
  show "reflp (relacion P)"
  proof (rule reflpI)
    fix x
    obtain A where "A ∈ P ∧ x ∈ A"
      using assms particion_def by metis
    then show "relacion P x x"
      using relacion_def by metis
  qed
next
  show "symp (relacion P)"
  proof (rule sympI)
    fix x y
    assume "relacion P x y"
    then obtain A where "A ∈ P ∧ x ∈ A ∧ y ∈ A"
      using relacion_def by metis
    then show "relacion P y x"
      using relacion_def by metis
  qed
next
  show "transp (relacion P)"
  proof (rule transpI)
    fix x y z
    assume "relacion P x y" and "relacion P y z"
    obtain A where "A ∈ P" and hA : "x ∈ A ∧ y ∈ A"
      using ‹relacion P x y› by (meson relacion_def)
    obtain B where "B ∈ P" and hB : "y ∈ B ∧ z ∈ B"
      using ‹relacion P y z› by (meson relacion_def)
    have "A = B"
    proof -
      obtain C where "C ∈ P"
                 and hC : "y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
        using assms particion_def by metis
      then show "A = B"
        using ‹A ∈ P› ‹B ∈ P› hA hB by blast
    qed
    then have "x ∈ A ∧ z ∈ A"  using hA hB by auto
    then show "relacion P x z"
      using ‹A = B› ‹A ∈ P› relacion_def by metis
  qed
qed

(* 2ª demostración *)

lemma
  assumes "particion P"
  shows   "equivp (relacion P)"
proof (rule equivpI)
  show "reflp (relacion P)"
    using assms particion_def relacion_def
    by (metis reflpI)
next
  show "symp (relacion P)"
    using assms relacion_def
    by (metis sympI)
next
  show "transp (relacion P)"
    using assms relacion_def particion_def
    by (smt (verit) transpI)
qed

end
</pre>
