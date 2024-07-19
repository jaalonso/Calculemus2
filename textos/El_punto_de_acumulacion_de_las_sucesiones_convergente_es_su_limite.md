---
title: El punto de acumulación de las sucesiones convergente es su límite
date: 2024-07-16 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
\\[ u_0, u_2, u_4, u_6, ... \\]
se ha obtenido con la función de extracción \\(φ\\) tal que \\(φ(n) = 2n\\).

En Lean4, se puede definir que \\(φ\\) es una función de extracción por
<pre lang="lean">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
que \\(a\\) es un límite de \\(u\\) por
<pre lang="lean">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>
que \\(u\\) es convergente por
<pre lang="lean">
   def convergente (u : ℕ → ℝ) :=
     ∃ a, limite u a
</pre>
que \\(a\\) es un punto de acumulación de \\(u\\) por
<pre lang="lean">
   def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
     ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
</pre>

Demostrar con Lean4 que si \\(u\\) es una sucesión convergente y \\(a\\) es un punto de acumulación de \\(u\\), entonces \\(a\\) es un límite de \\(u\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En la demostración usaremos los siguientes lemas demostrados en ejercicios anteriores:

+ Lema 1: El límite de una sucesión es único.
+ Lema 2: Las subsucesiones de las sucesiones convergentes tienen el mismo límite que la sucesión.

Puesto que \\(a\\) es un punto de acumulación de \\(u\\), existe una función de
extracción \\(φ\\) tal que
\\[ a \\text{ es límite de } u ∘ φ \\tag{1} \\]

Por otro lado, por ser \\(u\\) convergente, existe un \\(b\\) tal que
\\[ b \\text{ es límite de } u \\tag{2} \\]
Por el Lema 2,
\\[ b \\text{ es límite de } u ∘ φ \\tag{3} \\]

Por el Lema 1, (1) y (3)
\\[ a = b \\tag{4} \\]
Por (2) y (4)
\\[ a \\text{ es límite de } u \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- Usaremos los siguientes lemas demostrados en ejercicios anteriores.

lemma unicidad_limite_aux
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
by
  by_contra h
  -- h : ¬b ≤ a
  -- ⊢ False
  let ε := b - a
  cases' ha (ε/2) (by linarith) with A hA
  -- A : ℕ
  -- hA : ∀ (n : ℕ), n ≥ A → |u n - a| < ε / 2
  cases' hb (ε/2) (by linarith) with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), n ≥ B → |u n - b| < ε / 2
  let N := max A B
  have hAN : A ≤ N := le_max_left A B
  have hBN : B ≤ N := le_max_right A B
  specialize hA N hAN
  -- hA : |u N - a| < ε / 2
  specialize hB N hBN
  -- hB : |u N - b| < ε / 2
  rw [abs_lt] at hA hB
  -- hA : -(ε / 2) < u N - a ∧ u N - a < ε / 2
  -- hB : -(ε / 2) < u N - b ∧ u N - b < ε / 2
  linarith

lemma unicidad_limite
  {a b: ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (unicidad_limite_aux hb ha)
            (unicidad_limite_aux ha hb)

lemma limite_subsucesion_aux
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (φ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ φ m        := HI
         _ < φ (succ m) := h m (m+1) (lt_add_one m)

lemma limite_subsucesion
  {φ : ℕ → ℕ}
  {a : ℝ}
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' h ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have h1 : φ n ≥ N := calc
    φ n ≥ n := by exact limite_subsucesion_aux hφ n
      _ ≥ N := hn
  calc |(u ∘ φ ) n  - a| = |u (φ n) - a| := by exact rfl
                       _ < ε             := hN (φ n) h1

-- 1ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  unfold convergente at hu
  -- hu : ∃ a, limite u a
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  convert hb
  -- ⊢ a = b
  unfold punto_acumulacion at ha
  -- ha : ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
  rcases ha with ⟨φ, hφ₁, hφ₂⟩
  -- φ : ℕ → ℕ
  -- hφ₁ : extraccion φ
  -- hφ₂ : limite (u ∘ φ) a
  have hφ₃ : limite (u ∘ φ) b := limite_subsucesion hb hφ₁
  exact unicidad_limite hφ₂ hφ₃

-- 2ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  convert hb
  -- ⊢ a = b
  rcases ha with ⟨φ, hφ₁, hφ₂⟩
  -- φ : ℕ → ℕ
  -- hφ₁ : extraccion φ
  -- hφ₂ : limite (u ∘ φ) a
  apply unicidad_limite hφ₂ _
  -- ⊢ limite (u ∘ φ) b
  exact limite_subsucesion hb hφ₁

-- 3ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  convert hb
  -- ⊢ a = b
  rcases ha with ⟨φ, hφ₁, hφ₂⟩
  -- φ : ℕ → ℕ
  -- hφ₁ : extraccion φ
  -- hφ₂ : limite (u ∘ φ) a
  exact unicidad_limite hφ₂ (limite_subsucesion hb hφ₁)

-- Lemas usados
-- ============

-- variable (b : ℝ)
-- variable (m n : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (lt_add_one n : n < n + 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition subsucesion :: "(nat ⇒ real) ⇒ (nat ⇒ real) ⇒ bool"
  where "subsucesion v u ⟷ (∃ φ. extraccion φ ∧ v = u ∘ φ)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ < ε)"

definition convergente :: "(nat ⇒ real) ⇒ bool" where
  "convergente u ⟷ (∃ a. limite u a)"

definition punto_acumulacion :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "punto_acumulacion u a ⟷ (∃φ. extraccion φ ∧ limite (u ∘ φ) a)"

(* Lemas auxiliares *)

lemma unicidad_limite_aux :
  assumes "limite u a"
          "limite u b"
  shows   "b ≤ a"
proof (rule ccontr)
  assume "¬ b ≤ a"
  let ?ε = "b - a"
  have "0 < ?ε/2"
    using ‹¬ b ≤ a› by auto
  obtain A where hA : "∀n≥A. ¦u n - a¦ < ?ε/2"
    using assms(1) limite_def ‹0 < ?ε/2› by blast
  obtain B where hB : "∀n≥B. ¦u n - b¦ < ?ε/2"
    using assms(2) limite_def ‹0 < ?ε/2› by blast
  let ?C = "max A B"
  have hCa : "∀n≥?C. ¦u n - a¦ < ?ε/2"
    using hA by simp
  have hCb : "∀n≥?C. ¦u n - b¦ < ?ε/2"
    using hB by simp
  have "∀n≥?C. ¦a - b¦ < ?ε"
  proof (intro allI impI)
    fix n assume "n ≥ ?C"
    have "¦a - b¦ = ¦(a - u n) + (u n - b)¦" by simp
    also have "… ≤ ¦u n - a¦ + ¦u n - b¦" by simp
    finally show "¦a - b¦ < b - a"
      using hCa hCb ‹n ≥ ?C› by fastforce
  qed
  then show False by fastforce
qed

lemma unicidad_limite :
  assumes "limite u a"
          "limite u b"
  shows   "a = b"
proof (rule antisym)
  show "a ≤ b" using assms(2) assms(1)
    by (rule unicidad_limite_aux)
next
  show "b ≤ a" using assms(1) assms(2)
    by (rule unicidad_limite_aux)
qed

lemma limite_subsucesion_aux :
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0" by simp
next
  fix n assume HI : "n ≤ φ n"
  then show "Suc n ≤ φ (Suc n)"
    using assms extraccion_def
    by (metis Suc_leI lessI order_le_less_subst1)
qed

lemma limite_subsucesion :
  assumes "subsucesion v u"
          "limite u a"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "ε > 0"
  then obtain N where hN : "∀k≥N. ¦u k - a¦ < ε"
    using assms(2) limite_def by auto
  obtain φ where hφ1 : "extraccion φ" and hφ2 : "v = u ∘ φ"
    using assms(1) subsucesion_def by auto
  have "∀k≥N. ¦v k - a¦ < ε"
  proof (intro allI impI)
    fix k
    assume "N ≤ k"
    also have "... ≤ φ k"
      by (simp add: limite_subsucesion_aux hφ1)
    finally have "N ≤ φ k" .
    have "¦v k - a¦ = ¦u (φ k) - a¦"
      using hφ2 by simp
    also have "… < ε"
      using hN ‹N ≤ φ k› by simp
    finally show "¦v k - a¦ < ε" .
  qed
  then show "∃N. ∀k≥N. ¦v k - a¦ < ε"
    by auto
qed

(* Demostración *)

lemma
  assumes "convergente u"
          "punto_acumulacion u a"
  shows   "limite u a"
proof -
  obtain b where hb : "limite u b"
    using assms(1) convergente_def by auto
  obtain φ where hφ1 : "extraccion φ" and
                 hφ2 : "limite (u ∘ φ) a"
    using assms(2) punto_acumulacion_def  by auto
  have "limite (u ∘ φ) b"
    using hφ1 hb limite_subsucesion subsucesion_def by blast
  with hφ2 have "a = b"
    by (rule unicidad_limite)
  then show "limite u a"
    using hb by simp
qed

end
</pre>
