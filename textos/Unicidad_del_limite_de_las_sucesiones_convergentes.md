---
Título: Unicidad del límite de las sucesiones convergentes
Autor:  José A. Alonso
---

[mathjax]

En Lean, una sucesión \\(u₀, u₁, u₂, ...\\) se puede representar mediante una función \\((u : ℕ → ℝ)\\) de forma que \\(u(n)\\) es \\(uₙ\\).

Se define que \\(a\\) es el límite de la sucesión \\(u\\), por
<pre lang="text">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
     fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε
</pre>

Demostrar con Lean4 que cada sucesión tiene como máximo un límite.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {u : ℕ → ℝ}
variable {a b : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
  by sorry
</pre>

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que si \\(u\\) es una sucesión y \\(a\\) y \\(b\\) son límites de \\(u\\), entonces \\(a = b\\). Para ello, basta demostrar que \\(a ≤ b\\) y \\(b ≤ a\\).

Demostraremos que \\(b ≤ a\\) por reducción al absurdo. Supongamos que \\(b ≰ a\\). Sea \\(ε = b - a\\). Entonces, ε/2 > 0 y, puesto que \\(a\\) es un límite de \\(u\\), existe un \\(A ∈ ℕ\\) tal que
\\[ (∀n ∈ ℕ)\\left[n ≥ A → |u(n) - a| < \\frac{ε}{2}\\right] \\tag{1} \\]
y, puesto que \\(b\\) también es un límite de \\(u\\), existe un \\(B ∈ ℕ\\) tal que
\\[ (∀n ∈ ℕ)\\left[n ≥ B → |u(n) - b| < \\frac{ε}{2}\\right] \\tag{2} \\]
Sea \\(N = máx(A, B)\\). Entonces, \\(N ≥ A\\) y \\(N ≥ B\\) y, por (2) y (3), se tiene
\\begin{align}
    |u(N) - a| &< \\frac{ε}{2} \\tag{3} \\\\
    |u(N) - b| &< \\frac{ε}{2} \\tag{4}
\\end{align}
Para obtener una contradicción basta probar que \\(ε < ε\\). Su prueba es
\\begin{align}
   ε &= b - a                      \\\\
     &= |b - a|                    \\\\
     &= |(b - a) + (u(N) - u(N))|  \\\\
     &= |(u(N) - a) + (b - u(N))|  \\\\
     &≤ |u(N) - a| + |b - u(N)|    \\\\
     &= |u(N) - a| + |u(N) - b|    \\\\
     &< \\frac{ε}{2} + \\frac{ε}{2}    && \\text{[por (3) y (4)]} \\\\
     &= ε
\\end{align}

La demostración de \\(a ≤ b\\) es análoga a la anterior.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {u : ℕ → ℝ}
variable {a b : ℝ}

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración del lema auxiliar
-- =================================

example
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
by
  by_contra h
  -- h : ¬b ≤ a
  -- ⊢ False
  let ε := b - a
  have hε : ε > 0 := sub_pos.mpr (not_le.mp h)
  have hε2 : ε / 2 > 0 := half_pos hε
  cases' ha (ε/2) hε2 with A hA
  -- A : ℕ
  -- hA : ∀ (n : ℕ), n ≥ A → |u n - a| < ε / 2
  cases' hb (ε/2) hε2 with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), n ≥ B → |u n - b| < ε / 2
  let N := max A B
  have hAN : A ≤ N := le_max_left A B
  have hBN : B ≤ N := le_max_right A B
  specialize hA N hAN
  -- hA : |u N - a| < ε / 2
  specialize hB N hBN
  -- hB : |u N - b| < ε / 2
  have h2 : ε < ε := by calc
    ε = b - a                   := rfl
    _ = |b - a|                 := (abs_of_pos hε).symm
    _ = |(b - a) + 0|           := by {congr ; exact (add_zero (b - a)).symm}
    _ = |(b - a) + (u N - u N)| := by {congr ; exact (sub_self (u N)).symm}
    _ = |(u N - a) + (b - u N)| := congrArg (fun x => |x|) (by ring)
    _ ≤ |u N - a| + |b - u N|   := abs_add (u N - a) (b - u N)
    _ = |u N - a| + |u N - b|   := congrArg (|u N - a| + .) (abs_sub_comm b (u N))
    _ < ε / 2 + ε / 2           := add_lt_add hA hB
    _ = ε                       := add_halves ε
  have h3 : ¬(ε < ε) := lt_irrefl ε
  show False
  exact h3 h2

-- 2ª demostración del lema auxiliar
-- =================================

lemma aux
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

-- 1ª demostración
-- ===============

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (aux hb ha) (aux ha hb)

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (not_le : ¬a ≤ b ↔ b < a)
-- #check (sub_pos : 0 < a - b ↔ b < a)
-- #check (half_pos : a > 0 → a / 2 > 0)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
-- #check (abs_of_pos : 0 < a → |a| = a)
-- #check (add_zero a : a + 0 = a)
-- #check (sub_self a : a - a = 0)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (abs_sub_comm a b : |a - b| = |b - a|)
-- #check (add_lt_add : a < b → c < d → a + c < b + d)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (lt_irrefl a : ¬a < a)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Unicidad_del_limite_de_las_sucesiones_convergentes.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Unicidad_del_limite_de_las_sucesiones_convergentes
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma aux :
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

theorem
  assumes "limite u a"
          "limite u b"
  shows   "a = b"
proof (rule antisym)
  show "a ≤ b" using assms(2) assms(1) by (rule aux)
next
  show "b ≤ a" using assms(1) assms(2) by (rule aux)
qed

end
</pre>
