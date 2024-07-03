---
title: El conjunto de las clases de equivalencia es una partición
date: 2024-07-03 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Demostrar con Lean4 que si \\(R\\) es una relación de equivalencia en \\(X\\), entonces las clases de equivalencia de \\(R\\) es una partición de \\(X\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

def particion (P : Set (Set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

lemma aux
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
fun _ hz ↦ h.3 hxy hz

example
  (h : Equivalence R)
  : particion {a : Set X | ∃ s : X, a = clase R s} :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(P = {[x] : x ∈ X}\\). Tenemos que demostrar que \\(P\\) es una partición de \\(X\\); es decir, que
\\begin{align}
   &(∀x ∈ X)(∃B ∈ P)[x ∈ B ∧ (∀C ∈ P)[x ∈ C → B = C] \\tag{1} \\\\
   &∅ ∉ P                                            \\tag{2}
\\end{align}

Para demostrar (1) basta probar que
\\[ (∀x ∈ X)(∃y ∈ X)[x ∈ [y] ∧ (∀a ∈ X)[x ∈ [a] → [y] = [a]] \\tag{3} \\]
Para ello sea \\(x ∈ X\\). Veamos que \\([x]\\) cumple las condiciones de (3); es decir,
\\[ x ∈ [x] ∧ (∀a ∈ X)[x ∈ [a] → [x] = [a]] \\tag{4} \\]

La primera condición de (4) se verifica puesto que \\(R\\) es reflexiva.

Para probar la segunda parte de (4), sea \\(a ∈ X\\) tal que \\(x ∈ [a]\\); es decir,
\\[ aRx \\tag{5} \\]
y, puesto que \\(R\\) es simétrica,
\\[ xRa \\tag{6} \\]
Entonces,
\\begin{align}
   &z ∈ [x] &⟹ xRz        \\\\
   &        &⟹ aRz        &&\\tex{[por (5) y la transitividad de \\(R\\)]} \\\\
   &        &⟹ z ∈ [a]    \\\\
   &z ∈ [a] &⟹ aRz        \\\\
   &        &⟹ xRz        &&\\text{[por (6) y la transitividad de \\(R\\)]} \\\\
   &        &⟹ z ∈ [x]
\\end{align}
Por tanto, \\([x] = [a]\\).

Para demostrar (2), supongamos que \\(∅ ∈ P\\). Entonces, existe un \\(x ∈ X\\) tal
que \\([x] = ∅\\), lo cual es imposible porque \\(x ∈ [x]\\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

def particion (P : Set (Set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

lemma aux
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
fun _ hz ↦ h.3 hxy hz

-- 1ª demostración
-- ===============

example
  (h : Equivalence R)
  : particion {a : Set X | ∃ s : X, a = clase R s} :=
by
  set P := {a : Set X | ∃ s : X, a = clase R s}
  constructor
  . -- ⊢ (∀ x, ∃ B, B ∈ P) ∧ x ∈ B ∧ (∀ C, C ∈ P → x ∈ C → B = C)
    simp
    -- ⊢ (∀ x, ∃ B, (∃ s, B = clase R s)) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    intro x
    -- x : X
    -- ⊢ ∃ B, (∃ s, B = clase R s) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    use (clase R x)
    -- ⊢ (∃ s, clase R x = clase R s) ∧ x ∈ clase R x ∧ (∀ a, y ∈ clase R a → clase R x = clase R a)
    constructor
    . -- ⊢ ∃ s, clase R x = clase R s
      use x
    . --   x ∈ clase R x ∧
      --   ∀ a, x ∈ clase R a → clase R x = clase R a
      constructor
      . -- ⊢ x ∈ clase R x
        exact h.1 x
      . -- ∀ a, x ∈ clase R a → clase R x = clase R a
        intros a ha
        -- a : X
        -- ha : x ∈ clase R a
        -- ⊢ clase R x = clase R a
        apply le_antisymm
        . -- ⊢ clase R x ≤ clase R a
          exact aux h ha
        . -- ⊢ clase R a ≤ clase R x
          exact aux h (h.2 ha)
  . -- ⊢ ¬∅ ∈ P
    simp
    -- ⊢ ∀ (x : X), ¬∅ = clase R x
    intros x hx
    -- x : X
    -- hx : ∅ = clase R x
    -- ⊢ False
    have h1 : x ∈ clase R x := h.1 x
    rw [←hx] at h1
    -- h1 : x ∈ ∅
    exact Set.not_mem_empty x h1

-- 2ª demostración
-- ===============

example
  (h : Equivalence R)
  : particion {a : Set X | ∃ s : X, a = clase R s} :=
by
  set P := {a : Set X | ∃ s : X, a = clase R s}
  constructor
  . -- ⊢ (∀ x, ∃ B, B ∈ P) ∧ x ∈ B ∧ (∀ C, C ∈ P → x ∈ C → B = C)
    simp
    -- ⊢ (∀ x, ∃ B, (∃ s, B = clase R s)) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    intro x
    -- x : X
    -- ⊢ ∃ B, (∃ s, B = clase R s) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    use (clase R x)
    -- ⊢ (∃ s, clase R x = clase R s) ∧ x ∈ clase R y ∧ (∀ a, x ∈ clase R a → clase R x = clase R a)
    repeat' constructor
    . -- ⊢ x ∈ clase R x
      exact h.1 x
    . -- ⊢ ∀ a, x ∈ clase R a → clase R x = clase R a
      intros a ha
      -- a : X
      -- ha : y ∈ clase R a
      -- ⊢ clase R a = clase R a
      exact le_antisymm (aux h ha) (aux h (h.2 ha))
  . -- ⊢ ¬∅ ∈ P
    simp
    -- ⊢ ∀ (x : X), ¬∅ = clase R x
    intros x hx
    -- x : X
    -- hx : ∅ = clase R x
    -- ⊢ False
    have h1 : x ∈ clase R x := h.1 x
    rw [←hx] at h1
    -- h1 : x ∈ ∅
    exact Set.not_mem_empty x h1

-- Lemas usados
-- ============

-- variable (A B : Set X)
-- #check (Set.not_mem_empty x : x ∉ ∅)
-- #check (le_antisymm : A ≤ B → B ≤ A → A = B)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/El_conjunto_de_las_clases_de_equivalencia_es_una_particion.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory El_conjunto_de_las_clases_de_equivalencia_es_una_particion
imports Main
begin

definition clase :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a set"
  where "clase R x = {y. R x y}"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

lemma
  fixes   R :: "'a ⇒ 'a ⇒ bool"
  assumes "equivp R"
  shows   "particion (⋃x. {clase R x})" (is "particion ?P")
proof (unfold particion_def; intro conjI)
  show "(∀x. ∃B∈?P. x ∈ B ∧ (∀C∈?P. x ∈ C ⟶ B = C))"
  proof (intro allI)
    fix x
    have "clase R x ∈ ?P"
      by auto
    moreover have "x ∈ clase R x"
      using assms clase_def equivp_def
      by (metis CollectI)
    moreover have "∀C∈?P. x ∈ C ⟶ clase R x = C"
    proof
      fix C
      assume "C ∈ ?P"
      then obtain y where "C = clase R y"
        by auto
      show "x ∈ C ⟶ clase R x = C"
      proof
        assume "x ∈ C"
        then have "R y x"
          using ‹C = clase R y› assms clase_def
          by (metis CollectD)
        then show "clase R x = C"
          using assms ‹C = clase R y› clase_def equivp_def
          by metis
      qed
    qed
    ultimately show "∃B∈?P. x ∈ B ∧ (∀C∈?P. x ∈ C ⟶ B = C)"
      by blast
  qed
next
  show "{} ∉ ?P"
  proof
    assume "{} ∈ ?P"
    then obtain x where "{} = clase R x"
      by auto
    moreover have "x ∈ clase R x"
      using assms clase_def equivp_def
      by (metis CollectI)
    ultimately show False
      by simp
  qed
qed

end
</pre>
