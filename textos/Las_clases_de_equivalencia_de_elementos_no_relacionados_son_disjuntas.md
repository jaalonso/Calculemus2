---
title: Las clases de equivalencia de elementos no relacionados son disjuntas
date: 2024-07-02 06:00:00 UTC+02:00
category: Relaciones de equivalencia
has_math: true
---

[mathjax]

Demostrar con Lean4 que las clases de equivalencia de elementos no relacionados son disjuntas.

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
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sean \\(x, y ∈ X\\) tales que no están relacionados mediante la relación \\(R\\). Tenemos que demostrar que \\([x]\\) e \\([y]\\) son disjuntas; es decir,
\\[ (∀x)[z ∉ [x] ∩ [y]] \\]
Para ello, supongamos que un \\(z ∈ [x] ∩ [y]\\). Luego, \\(z ∈ [x]\\) y \\(z ∈ [y]\\); es decir, se tiene que
\\begin{align}
   &xRz \\tag{1} \\\\
   &yRz \\tag{2}
\\end{align}
De (2) y la simetría de \\(R\\), se tiene
\\[ zRy \\tag{3} \\]
De (1), (3) y la transitividad de \\(R\\), se tiene
\\[ xRy \\]
que es una contradicción,

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- 1ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by
  have h1 : ∀ z, ¬z ∈ clase R x ∩ clase R y := by
    intro z hz
    -- z : X
    -- hz : z ∈ clase R x ∩ clase R y
    have hxz : R x z := hz.1
    have hyz : R y z := hz.2
    have hzy : R z y := h.2 hyz
    have hxy2 : R x y := h.3 hxz hzy
    exact hxy hxy2
  exact Set.eq_empty_iff_forall_not_mem.mpr h1

-- 2ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by
  rcases h with ⟨-, hs, ht⟩
  -- hs : ∀ {x y : X}, R x y → R y x
  -- ht : ∀ {x y z : X}, R x y → R y z → R x z
  by_contra h1
  -- h1 : ¬clase R x ∩ clase R y = ∅
  -- ⊢ False
  apply hxy
  -- ⊢ R x y
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y
  . contrapose h1
    -- h1 : ¬∃ z, z ∈ clase R x ∩ clase R y
    -- ⊢ ¬¬clase R x ∩ clase R y = ∅
    push_neg
    push_neg at h1
    -- h1 : ∀ (z : X), ¬z ∈ clase R x ∩ clase R y
    exact Set.eq_empty_iff_forall_not_mem.mpr h1
  rcases h2 with ⟨z, hxz, hyz⟩
  -- z : X
  -- hxz : z ∈ clase R x
  -- hyz : z ∈ clase R y
  replace hxz : R x z := hxz
  replace hyz : R y z := hyz
  have hzy : R z y := hs hyz
  exact ht hxz hzy

-- 3ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by
  rcases h with ⟨-, hs, ht⟩
  -- hs : ∀ {x y : X}, R x y → R y x
  -- ht : ∀ {x y z : X}, R x y → R y z → R x z
  by_contra h1
  -- h1 : ¬clase R x ∩ clase R y = ∅
  -- ⊢ False
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y
  . aesop (add norm Set.eq_empty_iff_forall_not_mem)
  apply hxy
  -- ⊢ R x y
  rcases h2 with ⟨z, hxz, hyz⟩
  -- z : X
  -- hxz : z ∈ clase R x
  -- hyz : z ∈ clase R y
  exact ht hxz (hs hyz)

-- Lemas usados
-- ============

-- variable (s : Set X)
-- #check (Set.eq_empty_iff_forall_not_mem : s = ∅ ↔ ∀ x, x ∉ s)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas
imports Main
begin

definition clase :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a set"
  where "clase R x = {y. R x y}"

(* 1ª demostración *)

lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
proof -
  have "∀z. z ∈ clase R x ⟶ z ∉ clase R y"
  proof (intro allI impI)
    fix z
    assume "z ∈ clase R x"
    then have "R x z"
      using clase_def by (metis CollectD)
    show "z ∉ clase R y"
    proof (rule notI)
      assume "z ∈ clase R y"
      then have "R y z"
        using clase_def by (metis CollectD)
      then have "R z y"
        using assms(1) by (simp only: equivp_symp)
      with ‹R x z› have "R x y"
        using assms(1) by (simp only: equivp_transp)
      with ‹¬R x y› show False
        by (rule notE)
    qed
  qed
  then show "clase R x ∩ clase R y = {}"
    by (simp only: disjoint_iff)
qed

(* 2ª demostración *)

lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
proof -
  have "∀z. z ∈ clase R x ⟶ z ∉ clase R y"
  proof (intro allI impI)
    fix z
    assume "z ∈ clase R x"
    then have "R x z"
      using clase_def by fastforce
    show "z ∉ clase R y"
    proof (rule notI)
      assume "z ∈ clase R y"
      then have "R y z"
        using clase_def by fastforce
      then have "R z y"
        using assms(1) by (simp only: equivp_symp)
      with ‹R x z› have "R x y"
        using assms(1) by (simp only: equivp_transp)
      with ‹¬R x y› show False
        by simp
    qed
  qed
  then show "clase R x ∩ clase R y = {}"
    by (simp only: disjoint_iff)
qed

(* 3ª demostración *)

lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
  using assms
  by (metis clase_def
            CollectD
            equivp_symp
            equivp_transp
            disjoint_iff)

(* 4ª demostración *)

lemma
  assumes "equivp R"
          "¬(R x y)"
  shows "clase R x ∩ clase R y = {}"
  using assms
  by (metis equivp_def
            clase_def
            CollectD
            disjoint_iff_not_equal)

end
</pre>
