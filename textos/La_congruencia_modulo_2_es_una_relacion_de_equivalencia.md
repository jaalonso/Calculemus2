---
title: La congruencia módulo 2 es una relación de equivalencia
date: 2024-06-04 06:00:00 UTC+02:00
category: Relación de equivalencia
has_math: true
---

[mathjax]

Se define la relación \\(R\\) entre los números enteros de forma que \\(x\\) está relacionado con \\(y\\) si \\(x-y\\) es divisible por 2.

Demostrar con Lean4 que \\(R\\) es una relación de equivalencia.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

def R (m n : ℤ) := 2 ∣ (m - n)

example : Equivalence R :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que \\(\\text{ R }\\) es reflexiva, simétrica y transitiva.

Para demostrar que \\(\\text{ R }\\) es reflexiva, sea \\(x ∈ ℤ\\). Entonces, \\(x - x = 0\\) que es divisible por 2. Luego, \\(x\\text{ R }x\\).

Para demostrar que \\(\\text{ R }\\) es simétrica, sean \\(x, y ∈ ℤ\\) tales que \\(x\\text{ R }y\\). Entonces, \\(x - y\\) es divisible por 2. Luego, existe un \\(a ∈ ℤ\\) tal que
\\[ x - y = 2·a \\]
Por tanto,
\\[ y - x = 2·(-a) \\]
Por lo que \\(y - x\\) es divisible por 2 y \\(y\\text{ R }x\\).

Para demostrar que \\(\\text{ R }\\) es transitiva, sean \\(x, y, z ∈ ℤ\\) tales que \\(x\\text{ R }y\\) y \\(y\\text{ R }z\\). Entonces, tanto \\(x - y\\) como \\(y - z\\) son divibles por 2. Luego, existen \\(a, b ∈ ℤ\\) tales que
\\begin{align}
   x - y &= 2·a \\\\
   y - z &= 2·b
\\end{align}
Por tanto,
\\[ x - z = 2·(a + b) \\]
Por lo que \\(x - z\\) es divisible por 2 y \\(x\\text{ R }z\\}.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

def R (m n : ℤ) := 2 ∣ (m - n)

-- 1ª demostración
-- ===============

example : Equivalence R :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : ℤ), R x x
    intro x
    -- x : ℤ
    -- ⊢ R x x
    unfold R
    -- ⊢ 2 ∣ x - x
    rw [sub_self]
    -- ⊢ 2 ∣ 0
    exact dvd_zero 2
  . -- ⊢ ∀ {x y : ℤ}, R x y → R y x
    intros x y hxy
    -- x y : ℤ
    -- hxy : R x y
    -- ⊢ R y x
    unfold R at *
    -- hxy : 2 ∣ x - y
    -- ⊢ 2 ∣ y - x
    cases' hxy with a ha
    -- a : ℤ
    -- ha : x - y = 2 * a
    use -a
    -- ⊢ y - x = 2 * -a
    calc y - x
         = -(x - y) := (neg_sub x y).symm
       _ = -(2 * a) := by rw [ha]
       _ = 2 * -a   := neg_mul_eq_mul_neg 2 a
  . -- ⊢ ∀ {x y z : ℤ}, R x y → R y z → R x z
    intros x y z hxy hyz
    -- x y z : ℤ
    -- hxy : R x y
    -- hyz : R y z
    -- ⊢ R x z
    cases' hxy with a ha
    -- a : ℤ
    -- ha : x - y = 2 * a
    cases' hyz with b hb
    -- b : ℤ
    -- hb : y - z = 2 * b
    use a + b
    -- ⊢ x - z = 2 * (a + b)
    calc x - z
         = (x - y) + (y - z) := (sub_add_sub_cancel x y z).symm
       _ = 2 * a + 2 * b     := congrArg₂ (. + .) ha hb
       _ = 2 * (a + b)       := (mul_add 2 a b).symm

-- 2ª demostración
-- ===============

example : Equivalence R :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : ℤ), R x x
    intro x
    -- x : ℤ
    -- ⊢ R x x
    simp [R]
  . -- ⊢ ∀ {x y : ℤ}, R x y → R y x
    rintro x y ⟨a, ha⟩
    -- x y a : ℤ
    -- ha : x - y = 2 * a
    -- ⊢ R y x
    use -a
    -- ⊢ y - x = 2 * -a
    linarith
  . -- ⊢ ∀ {x y z : ℤ}, R x y → R y z → R x z
    rintro x y z ⟨a, ha⟩ ⟨b, hb⟩
    -- x y z a : ℤ
    -- ha : x - y = 2 * a
    -- b : ℤ
    -- hb : y - z = 2 * b
    -- ⊢ R x z
    use a + b
    -- ⊢ x - z = 2 * (a + b)
    linarith

-- Lemas usados
-- ============

-- variable (a b c x y x' y' : ℤ)
-- #check (congrArg₂  (. + .) : x = x' → y = y' → x + y = x' + y')
-- #check (dvd_zero a : a ∣ 0)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (neg_mul_eq_mul_neg a b : -(a * b) = a * -b)
-- #check (neg_sub a b : -(a - b) = b - a)
-- #check (sub_add_sub_cancel a b c : a - b + (b - c) = a - c)
-- #check (sub_self a : a - a = 0)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_congruencia_modulo_2_es_una_relacion_de_equivalencia.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_congruencia_modulo_2_es_una_relacion_de_equivalencia
imports Main
begin

definition R :: "(int × int) set" where
  "R = {(m, n). even (m - n)}"

lemma R_iff [simp]:
  "((x, y) ∈ R) = even (x - y)"
by (simp add: R_def)

(* 1ª demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show "R ⊆ UNIV × UNIV"
    proof -
      have "R ⊆ UNIV"
        by (rule top.extremum)
      also have "… = UNIV × UNIV"
        by (rule Product_Type.UNIV_Times_UNIV[symmetric])
      finally show "R ⊆ UNIV × UNIV"
        by this
    qed
  next
    show "∀x∈UNIV. (x, x) ∈ R"
    proof
      fix x :: int
      assume "x ∈ UNIV"
      have "even 0" by (rule even_zero)
      then have "even (x - x)" by (simp only: diff_self)
      then show "(x, x) ∈ R"
        by (simp only: R_iff)
    qed
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y :: int
    assume "(x, y) ∈ R"
    then have "even (x - y)"
      by (simp only: R_iff)
    then show "(y, x) ∈ R"
    proof (rule evenE)
      fix a :: int
      assume ha : "x - y = 2 * a"
      have "y - x = -(x - y)"
        by (rule minus_diff_eq[symmetric])
      also have "… = -(2 * a)"
        by (simp only: ha)
      also have "… = 2 * (-a)"
        by (rule mult_minus_right[symmetric])
      finally have "y - x = 2 * (-a)"
        by this
      then have "even (y - x)"
        by (rule dvdI)
      then show "(y, x) ∈ R"
        by (simp only: R_iff)
    qed
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume hxy : "(x, y) ∈ R" and hyz : "(y, z) ∈ R"
    have "even (x - y)"
      using hxy by (simp only: R_iff)
    then obtain a where ha : "x - y = 2 * a"
      by (rule dvdE)
    have "even (y - z)"
      using hyz by (simp only: R_iff)
    then obtain b where hb : "y - z = 2 * b"
      by (rule dvdE)
    have "x - z = (x - y) + (y - z)"
      by simp
    also have "… = (2 * a) + (2 * b)"
      by (simp only: ha hb)
    also have "… = 2 * (a + b)"
      by (simp only: distrib_left)
    finally have "x - z = 2 * (a + b)"
      by this
    then have "even (x - z)"
      by (rule dvdI)
    then show "(x, z) ∈ R"
      by (simp only: R_iff)
  qed
qed

(* 2ª demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show "R ⊆ UNIV × UNIV" by simp
  next
    show "∀x∈UNIV. (x, x) ∈ R"
    proof
      fix x :: int
      assume "x ∈ UNIV"
      have "x - x = 2 * 0"
        by simp
      then show "(x, x) ∈ R"
        by simp
    qed
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y :: int
    assume "(x, y) ∈ R"
    then have "even (x - y)"
      by simp
    then obtain a where ha : "x - y = 2 * a"
      by blast
    then have "y - x = 2 *(-a)"
      by simp
    then show "(y, x) ∈ R"
      by simp
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume hxy : "(x, y) ∈ R" and hyz : "(y, z) ∈ R"
    have "even (x - y)"
      using hxy by simp
    then obtain a where ha : "x - y = 2 * a"
      by blast
    have "even (y - z)"
      using hyz by simp
    then obtain b where hb : "y - z = 2 * b"
      by blast
    have "x - z = 2 * (a + b)"
      using ha hb by auto
    then show "(x, z) ∈ R"
      by simp
  qed
qed

(* 3ª demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show " R ⊆ UNIV × UNIV"
      by simp
  next
    show "∀x∈UNIV. (x, x) ∈ R"
      by simp
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y
    assume "(x, y) ∈ R"
    then show "(y, x) ∈ R"
      by simp
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume "(x, y) ∈ R" and "(y, z) ∈ R"
    then show "(x, z) ∈ R"
      by simp
  qed
qed

(* 4ª demostración *)

lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
    unfolding refl_on_def by simp
next
  show "sym R"
    unfolding sym_def by simp
next
  show "trans R"
    unfolding trans_def by simp
qed

(* 5ª demostración *)

lemma "equiv UNIV R"
  unfolding equiv_def refl_on_def sym_def trans_def
  by simp

(* 6ª demostración *)

lemma "equiv UNIV R"
  by (simp add: equiv_def refl_on_def sym_def trans_def)

end
</pre>
