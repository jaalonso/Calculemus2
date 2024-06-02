---
title: Si (∀n)[uₙ ≤ vₙ], entonces lim uₙ ≤ lim vₙ
date: 2024-05-31 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

En Lean4, una sucesión \\(u_0, u_1, u_2, \\dots\\) se puede representar mediante una función \\(u : ℕ → ℝ\\) de forma que \\(u(n)\\) es el \\(n\\)-ésimo término de la sucesión.

Se define que \\(a\\) límite de la sucesión \\(u\\) como sigue
<pre lang="isar">
   def limite (u : ℕ → ℝ) (c : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε
</pre>

Demostrar que si \\((∀ n)[u_n ≤ v_n]\\), \\(a\\) es límite de \\(u_n\\) y \\(c\\) es límite de \\(v_n\\), entonces \\(a ≤ c\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

example
  (hu : limite u a)
  (hv : limite v c)
  (huv : ∀ n, u n ≤ v n)
  : a ≤ c :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Por reduccion al absurdo. Supongamos que \\(a ≰ c\\). Entonces,
\\[ c < a \\tag{1} \\]
Sea
\\[ ε = \\frac{a - c}{2} \\tag{2} \\]
Por (1),
\\[ ε > 0 \\]
Por tanto, puesto que \\(a\\) es límite de \\(u_n\\), existe un \\(p ∈ ℕ\\) tal que
\\[ (∀ n)[n ≥ p → |u_n - a| < ε] \\tag{3} \\]
Análogamente, puesto que c es límite de \\(v_n\\), existe un \\(q ∈ ℕ\\) tal que
\\[ (∀ n)[n ≥ q → |v_n - c| < ε] \\tag{4} \\]
Sea
\\[ k = \\max(p, q) \\]
Entonces, \\(k ≥ p\\) y, por (3),
\\[ |u_k - a| < ε \\tag{5} \\]
Análogamente, \\(k ≥ q\\) y, por (4),
\\[ |v_k - c| < ε \\tag{6} \\]
Además, por la hipótesis,
\\[ u_k ≤ v_k \\tag{7} \\]
Por tanto,
\\begin{align}
   a - c &= (a - u_k) + (u_k - c)      \\\\
         &≤ (a - u_k) + (v_k - c)      &&\\text{[por (7)]} \\\\
         &≤ |(a - u_k) + (v_k - c)|    \\\\
         &≤ |a - u_k| + |v_k - c|      \\\\
         &= |u_k - a| + |v_k - c|      \\\\
         &< ε + ε                      &&\\text{[por (5) y (6)]} \\\\
         &= a - c                      &&\\text{[por (2)]}
\\end{align}
Luego,
\\[ a - c < a - c \\]
que es una contradicción.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic

variable (u v : ℕ → ℝ)
variable (a c : ℝ)

def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v c)
  (huv : ∀ n, u n ≤ v n)
  : a ≤ c :=
by
  by_contra h
  -- h : ¬a ≤ c
  -- ⊢ False
  have hca : c < a := not_le.mp h
  set ε := (a - c) /2
  have hε : 0 < ε := half_pos (sub_pos.mpr hca)
  obtain ⟨ku, hku : ∀ n, n ≥ ku → |u n - a| < ε⟩ := hu ε hε
  obtain ⟨kv, hkv : ∀ n, n ≥ kv → |v n - c| < ε⟩ := hv ε hε
  let k := max ku kv
  have hku' : ku ≤ k := le_max_left ku kv
  have hkv' : kv ≤ k := le_max_right ku kv
  have ha : |u k - a| < ε := hku k hku'
  have hc : |v k - c| < ε := hkv k hkv'
  have hk : u k - c ≤ v k - c := sub_le_sub_right (huv k) c
  have hac1 : a - c < a - c := by
    calc a - c
         = (a - u k) + (u k - c)   := by ring
       _ ≤ (a - u k) + (v k - c)   := add_le_add_left hk (a - u k)
       _ ≤ |(a - u k) + (v k - c)| := le_abs_self ((a - u k) + (v k - c))
       _ ≤ |a - u k| + |v k - c|   := abs_add (a - u k) (v k - c)
       _ = |u k - a| + |v k - c|   := by simp only [abs_sub_comm]
       _ < ε + ε                   := add_lt_add ha hc
       _ = a - c                   := add_halves (a - c)
  have hac2 : ¬ a - c < a -c := lt_irrefl (a - c)
  show False
  exact hac2 hac1

-- 2ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v c)
  (huv : ∀ n, u n ≤ v n)
  : a ≤ c :=
by
  by_contra h
  -- h : ¬a ≤ c
  -- ⊢ False
  have hca : c < a := not_le.mp h
  set ε := (a - c) /2 with hε
  obtain ⟨ku, hku : ∀ n, n ≥ ku → |u n - a| < ε⟩ := hu ε (by linarith)
  obtain ⟨kv, hkv : ∀ n, n ≥ kv → |v n - c| < ε⟩ := hv ε (by linarith)
  let k := max ku kv
  have ha : |u k - a| < ε := hku k (le_max_left ku kv)
  have hc : |v k - c| < ε := hkv k (le_max_right ku kv)
  have hk : u k - c ≤ v k - c := sub_le_sub_right (huv k) c
  have hac1 : a - c < a -c := by
    calc a - c
         = (a - u k) + (u k - c)   := by ring
       _ ≤ (a - u k) + (v k - c)   := add_le_add_left hk (a - u k)
       _ ≤ |(a - u k) + (v k - c)| := le_abs_self ((a - u k) + (v k - c))
       _ ≤ |a - u k| + |v k - c|   := abs_add (a - u k) (v k - c)
       _ = |u k - a| + |v k - c|   := by simp only [abs_sub_comm]
       _ < ε + ε                   := add_lt_add ha hc
       _ = a - c                   := add_halves (a - c)
  have hac2 : ¬ a - c < a -c := lt_irrefl (a - c)
  show False
  exact hac2 hac1

-- 3ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v c)
  (huv : ∀ n, u n ≤ v n)
  : a ≤ c :=
by
  by_contra h
  -- h : ¬a ≤ c
  -- ⊢ False
  have hca : c < a := not_le.mp h
  set ε := (a - c) /2 with hε
  obtain ⟨ku, hku : ∀ n, n ≥ ku → |u n - a| < ε⟩ := hu ε (by linarith)
  obtain ⟨kv, hkv : ∀ n, n ≥ kv → |v n - c| < ε⟩ := hv ε (by linarith)
  let k := max ku kv
  have ha : |u k - a| < ε := hku k (le_max_left ku kv)
  have hc : |v k - c| < ε := hkv k (le_max_right ku kv)
  have hk : u k - c ≤ v k - c := sub_le_sub_right (huv k) c
  have hac1 : a - c < a -c := by
    calc a - c
         = (a - u k) + (u k - c)   := by ring
       _ ≤ (a - u k) + (v k - c)   := add_le_add_left hk (a - u k)
       _ ≤ |(a - u k) + (v k - c)| := by simp [le_abs_self]
       _ ≤ |a - u k| + |v k - c|   := by simp [abs_add]
       _ = |u k - a| + |v k - c|   := by simp [abs_sub_comm]
       _ < ε + ε                   := add_lt_add ha hc
       _ = a - c                   := by simp
  have hac2 : ¬ a - c < a -c := lt_irrefl (a - c)
  show False
  exact hac2 hac1

-- 4ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v c)
  (huv : ∀ n, u n ≤ v n)
  : a ≤ c :=
by
  apply le_of_not_lt
  -- ⊢ ¬c < a
  intro hca
  -- hca : c < a
  -- ⊢ False
  set ε := (a - c) /2 with hε
  cases' hu ε (by linarith) with ku hku
  -- ku : ℕ
  -- hku : ∀ (n : ℕ), n ≥ ku → |u n - a| < ε
  cases' hv ε (by linarith) with kv hkv
  -- kv : ℕ
  -- hkv : ∀ (n : ℕ), n ≥ kv → |v n - c| < ε
  let k := max ku kv
  have ha : |u k - a| < ε := hku k (le_max_left ku kv)
  have hc : |v k - c| < ε := hkv k (le_max_right ku kv)
  have hk : u k ≤ v k := huv k
  apply lt_irrefl (a - c)
  -- ⊢ a - c < a - c
  rw [abs_lt] at ha hc
  -- ha : -ε < u k - a ∧ u k - a < ε
  -- hc : -ε < v k - c ∧ v k - c < ε
  linarith

-- Lemas usados
-- ============

-- variable (b d : ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_lt: |a| < b ↔ -b < a ∧ a < b)
-- #check (abs_sub_comm a b : |a - b| = |b - a|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (add_le_add_left : b ≤ c → ∀ a, a + b ≤ a + c)
-- #check (add_lt_add : a < b → c < d → a + c < b + d)
-- #check (half_pos : 0 < a → 0 < a / 2)
-- #check (le_abs_self a : a ≤ |a|)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (le_of_not_lt :  ¬b < a → a ≤ b)
-- #check (lt_irrefl a : ¬a < a)
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (sub_le_sub_right : a ≤ b → ∀ c, a - c ≤ b - c)
-- #check (sub_pos : 0 < a - b ↔ b < a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Limite_de_sucesion_menor_que_otra_sucesion.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Limite_de_sucesion_menor_que_otra_sucesion
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma
  assumes "limite u a"
          "limite v c"
          "∀n. u n ≤ v n"
  shows   "a ≤ c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?ε = "(a - c) /2"
  have "0 < ?ε"
    using ‹c < a› by simp
  obtain Nu where HNu : "∀n≥Nu. ¦u n - a¦ < ?ε"
    using assms(1) limite_def ‹0 < ?ε› by blast
  obtain Nv where HNv : "∀n≥Nv. ¦v n - c¦ < ?ε"
    using assms(2) limite_def ‹0 < ?ε› by blast
  let ?N = "max Nu Nv"
  have "?N ≥ Nu"
    by simp
  then have Ha : "¦u ?N - a¦ < ?ε"
    using HNu by simp
  have "?N ≥ Nv"
    by simp
  then have Hc : "¦v ?N - c¦ < ?ε"
    using HNv by simp
  have "a - c < a - c"
  proof -
    have "a - c = (a - u ?N) + (u ?N - c)"
      by simp
    also have "… ≤ (a - u ?N) + (v ?N - c)"
      using assms(3) by auto
    also have "… ≤ ¦(a - u ?N) + (v ?N - c)¦"
      by (rule abs_ge_self)
    also have "… ≤ ¦a - u ?N¦ + ¦v ?N - c¦"
      by (rule abs_triangle_ineq)
    also have "… = ¦u ?N - a¦ + ¦v ?N - c¦"
      by (simp only: abs_minus_commute)
    also have "… < ?ε + ?ε"
      using Ha Hc by (simp only: add_strict_mono)
    also have "… = a - c"
      by (rule field_sum_of_halves)
    finally show "a - c < a - c"
      by this
  qed
  have "¬ a - c < a - c"
    by (rule less_irrefl)
  then show False
    using ‹a - c < a - c› by (rule notE)
qed

(* 2ª demostración *)

lemma
  assumes "limite u a"
          "limite v c"
          "∀n. u n ≤ v n"
  shows   "a ≤ c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?ε = "(a - c) /2"
  have "0 < ?ε"
    using ‹c < a› by simp
  obtain Nu where HNu : "∀n≥Nu. ¦u n - a¦ < ?ε"
    using assms(1) limite_def ‹0 < ?ε› by blast
  obtain Nv where HNv : "∀n≥Nv. ¦v n - c¦ < ?ε"
    using assms(2) limite_def ‹0 < ?ε› by blast
  let ?N = "max Nu Nv"
  have "?N ≥ Nu"
    by simp
  then have Ha : "¦u ?N - a¦ < ?ε"
    using HNu by simp
  then have Ha' : "u ?N - a < ?ε ∧ -(u ?N - a) < ?ε"
    by argo
  have "?N ≥ Nv"
    by simp
  then have Hc : "¦v ?N - c¦ < ?ε"
    using HNv by simp
  then have Hc' : "v ?N - c < ?ε ∧ -(v ?N - c) < ?ε"
    by argo
  have "a - c < a - c"
    using assms(3) Ha' Hc'
    by (smt (verit, best) field_sum_of_halves)
  have "¬ a - c < a - c"
    by simp
  then show False
    using ‹a - c < a - c› by simp
qed

(* 3ª demostración *)

lemma
  assumes "limite u a"
          "limite v c"
          "∀n. u n ≤ v n"
  shows   "a ≤ c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?ε = "(a - c) /2"
  have "0 < ?ε"
    using ‹c < a› by simp
  obtain Nu where HNu : "∀n≥Nu. ¦u n - a¦ < ?ε"
    using assms(1) limite_def ‹0 < ?ε› by blast
  obtain Nv where HNv : "∀n≥Nv. ¦v n - c¦ < ?ε"
    using assms(2) limite_def ‹0 < ?ε› by blast
  let ?N = "max Nu Nv"
  have "?N ≥ Nu"
    by simp
  then have Ha : "¦u ?N - a¦ < ?ε"
    using HNu by simp
  then have Ha' : "u ?N - a < ?ε ∧ -(u ?N - a) < ?ε"
    by argo
  have "?N ≥ Nv"
    by simp
  then have Hc : "¦v ?N - c¦ < ?ε"
    using HNv by simp
  then have Hc' : "v ?N - c < ?ε ∧ -(v ?N - c) < ?ε"
    by argo
  show False
    using assms(3) Ha' Hc'
    by (smt (verit, best) field_sum_of_halves)
qed

end
</pre>
