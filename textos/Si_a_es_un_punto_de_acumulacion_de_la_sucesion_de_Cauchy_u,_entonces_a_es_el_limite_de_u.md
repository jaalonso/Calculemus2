---
title: Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u
date: 2024-07-25 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, una sucesión \\(u_0, u_1, u_2, u_3 ...\\) se puede representar mediante una función \\(u : ℕ → ℝ) de forma que \\(u(n)\\) es el término \\(u_n\\).

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión \\(u_0, u_2, u_4, u_6, ...\\) se ha obtenido con la función de extracción \\(φ\\) tal que \\(φ(n) = 2n\\).

En Lean4, se puede definir que \\(φ\\) es una función de extracción por
<pre lang="lean">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
que a es un límite de u por
<pre lang="lean">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>
que a es un punto de acumulación de u por
<pre lang="lean">
   def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
     ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
</pre>
que la sucesión u es de Cauchy por
<pre lang="lean">
   def suc_cauchy (u : ℕ → ℝ) :=
     ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε
</pre>

Demostrar con Lean4 que si \\(u\\) es una sucesión de Cauchy y \\(a\\) es un punto de acumulación de \\(u\\), entonces \\(a\\) es el límite de \\(u\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}

example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En la demostración usaremos el siguiente lema demostrado en un ejercicio anterior: Si \\(a\\) es un punto de acumulación de \\(u\\), entonces
\\[ (∀ ε > 0)(∀ N)(∃ n ≥ N) |u n - a| < ε \\]

Sea \\(ε > 0\\). Por ser u una sucesión de Cauchy, existe un \\(N ∈ ℕ\\) tal que
\\[ (∀ p ≥ N)(∀ q ≥ N)|u(p) - u(q)| < ε/2 \\tag{1} \\]
Vamos a demostrar que
\\[ (∀ n ≥ N)|u(n) - a| < ε \\]
y, por tanto \\(a\\) es limite de \\(u\\).

Para ello, sea \\(n ∈ ℕ\\) tal que
\\[ n ≥ N \\tag{2} \\]
Por el lema, existe un \\(N' ∈ ℕ\\) tal que
\\begin{align}
   &N' ≥ N              \\tag{3} \\\\
   &|u(N') - a| < ε/2   \\tag{4}
\\end{align}
Por tanto,
\\begin{align}
   |u(n) - a| &= |(u(n) - u(N')) + (u(N') - a)|  \\\\
              &≤ |u(n) - u(N')| + |u(N') - a|    \\\\
              &< ε/2 + |u(N') - a|               &&\\text{[por (1), (2) y (3)]} \\\\
              &< ε/2 + ε/2                       &&\\text{[por (4)]} \\\\
              &= ε
\\end{align}
De donde se tiene que
\\[ |u(n) - a| < ε \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}
variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

lemma aux1
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (φ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ φ m        := HI
         _ < φ (succ m) := h m (m+1) (lt_add_one m)

lemma aux2
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
fun N N' ↦ ⟨max N N', ⟨le_max_right N N',
                       le_trans (le_max_left N N')
                                (aux1 h (max N N'))⟩⟩

lemma cerca_acumulacion
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
by
  intros ε hε N
  rcases h with ⟨φ, hφ1, hφ2⟩
  cases' hφ2 ε hε with N' hN'
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩
  exact ⟨φ m, hm', hN' _ hm⟩

-- 1ª demostración
-- ===============

example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  unfold limite
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  unfold suc_cauchy at hu
  -- hu : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε
  cases' hu (ε/2) (half_pos hε) with N hN
  -- N : ℕ
  -- hN : ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε / 2
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2 :=
    cerca_acumulacion ha (ε/2) (half_pos hε) N
  cases' ha' with N' h
  -- N' : ℕ
  -- h : N' ≥ N ∧ |u N' - a| < ε / 2
  cases' h with hNN' hN'
  -- hNN' : N' ≥ N
  -- hN' : |u N' - a| < ε / 2
  calc   |u n - a|
       = |(u n - u N') + (u N' - a)| := by ring_nf
     _ ≤ |u n - u N'| + |u N' - a|   := abs_add (u n - u N') (u N' - a)
     _ < ε/2 + |u N' - a|            := add_lt_add_right (hN n hn N' hNN') _
     _ < ε/2 + ε/2                   := add_lt_add_left hN' (ε / 2)
     _ = ε                           := add_halves ε

-- 2ª demostración
-- ===============

example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  cases' hu (ε/2) (by linarith) with N hN
  -- N : ℕ
  -- hN : ∀ (p : ℕ), p ≥ N → ∀ (q : ℕ), q ≥ N → |u p - u q| < ε / 2
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |u n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |u n - a| < ε
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2 := by
    apply cerca_acumulacion ha (ε/2) (by linarith)
  rcases ha' with ⟨N', hNN', hN'⟩
  -- N' : ℕ
  -- hNN' : N' ≥ N
  -- hN' : |u N' - a| < ε / 2
  calc  |u n - a|
      = |(u n - u N') + (u N' - a)| := by ring_nf
    _ ≤ |u n - u N'| + |u N' - a|   := abs_add (u n - u N') (u N' - a)
    _ < ε                           := by linarith [hN n hn N' hNN']

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- variable (b c : ℝ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (add_lt_add_left : b < c → ∀ (a : ℝ), a + b < a + c)
-- #check (add_lt_add_right : b < c → ∀ (a : ℝ), b + a < c + a)
-- #check (half_pos : 0 < a → 0 < a / 2)
-- #check (le_max_left m n : m ≤ max m n)
-- #check (le_max_right m n : n ≤ max m n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u"
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition punto_acumulacion :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "punto_acumulacion u a ⟷ (∃φ. extraccion φ ∧ limite (u ∘ φ) a)"

definition suc_cauchy :: "(nat ⇒ real) ⇒ bool"
  where "suc_cauchy u ⟷ (∀ε>0. ∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε)"

(* Lemas auxiliares *)

lemma aux1 :
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

lemma aux2 :
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  have "max N N' ≥ N' ∧ φ (max N N') ≥ N"
    by (meson assms aux1 max.bounded_iff max.cobounded2)
  then show "∃k ≥ N'. φ k ≥ N"
    by blast
qed

lemma cerca_acumulacion :
  assumes "punto_acumulacion u a"
  shows   "∀ε>0. ∀ N. ∃k≥N. ¦u k - a¦ < ε"
proof (intro allI impI)
  fix ε :: real and N :: nat
  assume "ε > 0"
  obtain φ where hφ1 : "extraccion φ"
             and hφ2 : "limite (u ∘ φ) a"
    using assms punto_acumulacion_def by blast
  obtain N' where hN' : "∀k≥N'. ¦(u ∘ φ) k - a¦ < ε"
    using hφ2 limite_def ‹ε > 0› by auto
  obtain m where "m ≥ N' ∧ φ m ≥ N"
    using aux2 hφ1 by blast
  then show "∃k≥N. ¦u k - a¦ < ε"
    using hN' by auto
qed

(* Demostración *)

lemma
  assumes "suc_cauchy u"
          "punto_acumulacion u a"
  shows   "limite u a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "ε > 0"
  then have "ε/2 > 0"
    by simp
  then obtain N where hN : "∀m≥N. ∀n≥N. ¦u m - u n¦ < ε/2"
    using assms(1) suc_cauchy_def
    by blast
  have "∀k≥N. ¦u k - a¦ < ε"
  proof (intro allI impI)
    fix k
    assume hk : "k ≥ N"
    obtain N' where hN'1 : "N' ≥ N" and
                    hN'2 : "¦u N' - a¦ < ε/2"
      using assms(2) cerca_acumulacion ‹ε/2 > 0› by blast
    have "¦u k - a¦ = ¦(u k - u N') + (u N'  - a)¦"
      by simp
    also have "… ≤ ¦u k - u N'¦ + ¦u N'  - a¦"
      by simp
    also have "… < ε/2 + ¦u N'  - a¦"
      using hk hN hN'1 by auto
    also have "… < ε/2 + ε/2"
      using hN'2 by auto
    also have "… = ε"
      by simp
    finally show "¦u k - a¦ < ε" .
  qed
  then show "∃N. ∀k≥N. ¦u k - a¦ < ε"
    by auto
qed

end
</pre>
