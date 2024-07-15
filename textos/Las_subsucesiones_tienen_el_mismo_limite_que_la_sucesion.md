---
title: Las subsucesiones tienen el mismo límite que la sucesión
date: 2024-07-15 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
\\[ u_0, u_3, u_4, u_6, ... \\]
se ha obtenido con la función de extracción \\(φ\\) tal que \\(φ(n) = 2n\\).

En Lean4, se puede definir que \\(φ\\) es una función de extracción por
<pre lang="lean">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
que \\(v\\) es una subsucesión de \\(u\\) por
<pre lang="lean">
   def subsucesion (v u : ℕ → ℝ) :=
     ∃ φ, extraccion φ ∧ v = u ∘ φ
</pre>
y que \\(a\\) es un límite de \\(u\\) por
<pre lang="lean">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>

Demostrar con Lean4 que las subsucesiones de una sucesión convergente tienen el mismo límite que la sucesión.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u v : ℕ → ℝ}
variable {a : ℝ}
variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Usaremos el siguiente lema demostrado en un ejercicio anterior: Si \\(φ\\) es una función de extracción, entonces
\\[ (∀ n)[n ≤ φ(n)] \\]

Por ser \\(v\\) una subsucesión de \\(u\\), existe una función de extracción \\(φ\\) tal que
\\[ v = u ∘ φ \\tag{1} \\]
Sea \\(a\\) el límite de \\(u\\) y tenemos que demostrar que también lo es de \\(v\\). Para ello, sea \\(ε > 0\\). Por ser \\(a\\) límite de \\(u\\), existe un \\(N ∈ ℕ\\) tal que
\\[ (∀ k ≥ N)[|u(k) - a| < ε] \\tag{2} \\]
Vamos a demostrar que
\\[ (∀ n ≥ N)[|v(n) - a| < ε] \\]
Para ello, sea \\(n ≥ N\\). Entonces,
\\[ φ(n) ≥ N \\tag{3} \\]
ya que
\\begin{align}
   φ(n) &≥ n    &&\\text{[por el Lema]} \\\\
        &≥ N
\\end{align}
Luego,
\\begin{align}
   |v(n) - a| &= |(u ∘ φ )(n) - a|    &&text{[por (1)]} \\\\
              &= |u(φ(n)) - a|        \\\\
              &< ε                    &&text{[por (2) y (3)]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u v : ℕ → ℝ}
variable {a : ℝ}
variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

-- En la demostración se usará el siguiente lema demostrado en un
-- ejercicio anterior.
lemma aux
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (φ 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ φ m        := HI
         _ < φ (succ m) := h m (m+1) (lt_add_one m)

-- 1ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have h1 : φ n ≥ N := calc
    φ n ≥ n := by exact aux hφ1 n
      _ ≥ N := hn
  calc |v n  - a| = |(u ∘ φ ) n  - a| := by {congr ; exact congrFun hφ2 n}
                _ = |u (φ n) - a|     := rfl
                _ < ε                 := hN (φ n) h1

-- 2ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  unfold limite
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  unfold limite at ha
  -- ha : ∀ (ε : ℝ), ε > 0 → ∃ N, ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  unfold subsucesion at hv
  -- hv : ∃ φ, extraccion φ ∧ v = u ∘ φ
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ |(u ∘ φ) n - a| < ε
  apply hN
  -- ⊢ φ n ≥ N
  apply le_trans hn
  -- ⊢ n ≤ φ n
  exact aux hφ1 n

-- 3ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |v n - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ |(u ∘ φ) n - a| < ε
  apply hN
  -- ⊢ φ n ≥ N
  exact le_trans hn (aux hφ1 n)

-- 4ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |v n - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ |(u ∘ φ) n - a| < ε
  exact hN (φ n) (le_trans hn (aux hφ1 n))

-- 5ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |(u ∘ φ) k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |(u ∘ φ) k - a| < ε
  exact fun n hn ↦ hN (φ n) (le_trans hn (aux hφ1 n))

-- 6ª demostración
-- ===============

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' ha ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  rcases hv with ⟨φ, hφ1, hφ2⟩
  -- φ : ℕ → ℕ
  -- hφ1 : extraccion φ
  -- hφ2 : v = u ∘ φ
  rw [hφ2]
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |(u ∘ φ) k - a| < ε
  exact ⟨N, fun n hn ↦ hN (φ n) (le_trans hn (aux hφ1 n))⟩

-- Lemas usados
-- ============

-- variable (m n x y z : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (lt_add_one n : n < n + 1)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition subsucesion :: "(nat ⇒ real) ⇒ (nat ⇒ real) ⇒ bool"
  where "subsucesion v u ⟷ (∃ φ. extraccion φ ∧ v = u ∘ φ)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

(* En la demostración se usará el siguiente lema *)

lemma aux :
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

(* Demostración *)

lemma
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
      by (simp add: aux hφ1)
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

end
</pre>
