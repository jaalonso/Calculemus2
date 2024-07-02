---
title: Las clases de equivalencia de elementos relacionados son iguales
date: 2024-07-01 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Demostrar con Lean4 que las clases de equivalencia de elementos relacionados son iguales.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(x, y ∈ X\\) tales que
\\[ xRy \\tag{1} \\]
Tenemos que demostrar que \\([x] = [y]\\); es decir, que
\\begin{align}
   &[y] ⊆ [x] \\tag{2} \\\\
   &[x] ⊆ [y] \\tag{3}
\\end{align}

Para demostrar (2), sea \\(z ∈ [y]\\). Entonces,
\\[ yRz \\]
entonces, por (1) y por ser \\(R\\) transitiva,
\\[ xRz \\]
Luego, \\(z ∈ [x]\\).

Para demostrar (2), se observa que por (1) y por ser \\(R\\) simétrica, se tiene que \\(yRx\\) y se puede usar el mismo razonamiento del caso anterior.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- En la demostración se usará el siguiente lema del que se presentan
-- varias demostraciones.

-- 1ª demostración del lema auxiliar
-- =================================

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
by
  intros z hz
  -- z : X
  -- hz : z ∈ clase R y
  -- ⊢ z ∈ clase R x
  have hyz : R y z := hz
  have htrans : Transitive R := Equivalence.transitive h
  have hxz : R x z := htrans hxy hyz
  exact hxz

-- 2ª demostración del lema auxiliar
-- =================================

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
by
  intros z hz
  -- z : X
  -- hz : z ∈ clase R y
  -- ⊢ z ∈ clase R x
  exact (Equivalence.transitive h) hxy hz

-- 3ª demostración del lema auxiliar
-- =================================

lemma aux
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
fun _ hz ↦ (Equivalence.transitive h) hxy hz

-- A continuación se presentan varias demostraciones del ejercicio
-- usando el lema auxiliar

-- 1ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
by
  apply le_antisymm
  . -- ⊢ clase R x ≤ clase R y
    have hs : Symmetric R := Equivalence.symmetric h
    have hyx : R y x := hs hxy
    exact aux h hyx
  . -- ⊢ clase R y ≤ clase R x
    exact aux h hxy

-- 2ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
by
  apply le_antisymm
  . -- ⊢ clase R x ≤ clase R y
    exact aux h (Equivalence.symmetric h hxy)
  . -- ⊢ clase R y ≤ clase R x
    exact aux h hxy

-- 3ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
le_antisymm (aux h (Equivalence.symmetric h hxy)) (aux h hxy)

-- Lemas usados
-- ============

-- variable (x y z : Set X)
-- #check (Equivalence.symmetric : Equivalence R → Symmetric R)
-- #check (Equivalence.transitive : Equivalence R → Transitive R)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales
imports Main
begin

definition clase :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a set"
  where "clase R x = {y. R x y}"

(* En la demostración se usará el siguiente lema del que se presentan
   varias demostraciones. *)

(* 1ª demostración del lema auxiliar *)

lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y ⊆ clase R x"
proof (rule subsetI)
  fix z
  assume "z ∈ clase R y"
  then have "R y z"
    by (simp add: clase_def)
  have "transp R"
    using assms(1) by (rule equivp_imp_transp)
  then have "R x z"
    using ‹R x y› ‹R y z› by (rule transpD)
  then show "z ∈ clase R x"
    by (simp add: clase_def)
qed

(* 2ª demostración del lema auxiliar *)

lemma aux :
  assumes "equivp R"
          "R x y"
  shows "clase R y ⊆ clase R x"
  using assms
  by (metis clase_def eq_refl equivp_def)

(* A continuación se presentan demostraciones del ejercicio *)

(* 1ª demostración *)

lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y = clase R x"
proof (rule equalityI)
  show "clase R y ⊆ clase R x"
    using assms by (rule aux)
next
  show "clase R x ⊆ clase R y"
  proof -
    have "symp R"
      using assms(1) equivpE by blast
    have "R y x"
      using ‹R x y› by (simp add: ‹symp R› sympD)
    with assms(1) show "clase R x ⊆ clase R y"
       by (rule aux)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "equivp R"
          "R x y"
  shows "clase R y = clase R x"
  using assms
  by (metis clase_def equivp_def)

end
</pre>
