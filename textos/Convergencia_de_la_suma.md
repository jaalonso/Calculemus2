---
Título: Si la sucesión u converge a a y la v a b, entonces u+v converge a a+b
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si la sucesión \\(u\\) converge a \\(a\\) y la \\(v\\) a \\(b\\), entonces \\(u+v\\) converge a \\(a+b\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {s t : ℕ → ℝ} {a b c : ℝ}

def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En la demostración usaremos los siguientes lemas
\\begin{align}
   &(∀ a ∈ ℝ)\\left[a > 0 → \\frac{a}{2} > 0\\right]        \\tag{L1} \\\\
   &(∀ a, b, c ∈ ℝ)[\\max(a, b) ≤ c → a ≤ c]    \\tag{L2} \\\\
   &(∀ a, b, c ∈ ℝ)[\\max(a, b) ≤ c → b ≤ c]    \\tag{L3} \\\\
   &(∀ a, b ∈ ℝ)[|a + b| ≤ |a| + |b|]         \\tag{L4} \\\\
   &(∀ a ∈ ℝ)\\left[\\frac{a}{2} + \\frac{a}{2} = a\\right]  \\tag{L5}
\\end{align}

Tenemos que probar que para todo \\(ε ∈ ℝ\\), si
\\[ ε > 0 \\tag{1} \\]
entonces
\\[ (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |(u + v)(n) - (a + b)| < ε] \\tag{2} \\]

Por (1) y el lema L1, se tiene que
\\[ \\frac{ε}{2} > 0 \\tag{3} \\]
Por (3) y porque el límite de \\(u\\) es \\(a\\), se tiene que
\\[ (∃N ∈ ℕ)(∀n ∈ ℕ)\\left[n ≥ N → |u(n) - a| < \\frac{ε}{2}\\right] \\]
Sea \\(N₁ ∈ ℕ\\) tal que
\\[ (∀n ∈ ℕ)\\left[n ≥ N₁ → |u(n) - a| < \\frac{ε}{2}\\right] \\tag{4} \\]
Por (3) y porque el límite de \\(v\\) es \\(b\\), se tiene que
\\[ (∃N ∈ ℕ)(∀n ∈ ℕ)\\left[n ≥ N → |v(n) - b| < \\frac{ε}{2}\\right] \\]
Sea \\(N₂ ∈ ℕ\\) tal que
\\[ (∀n ∈ ℕ)\\left[n ≥ N₂ → |v(n) - b| < \\frac{ε}{2}\\right] \\tag{5} \\]
Sea \\(N = \\max(N₁, N₂)\\). Veamos que verifica la condición (1). Para ello, sea \\(n ∈ ℕ\\) tal que \\(n ≥ N\\). Entonces, \\(n ≥ N₁\\) (por L2) y \\(n ≥ N₂\\) (por L3). Por tanto, usando las propiedades (4) y (5) se tiene que
\\begin{align}
   |u(n) - a| &< \\frac{ε}{2} \\tag{6} \\\\
   |v(n) - b| &< \\frac{ε}{2} \\tag{7}
\\end{align}
Finalmente,
\\begin{align}
   |(u + v)(n) - (a + b)| &= |(u(n) + v(n)) - (a + b)|    \\\\
                          &= |(u(n) - a) + (v(n) - b)|    \\\\
                          &≤ |u(n) - a| + |v(n) - b|      &&\\text{[por L4]}\\\\
                          &< \\frac{ε}{2} + \\frac{ε}{2}    &&\\text{[por (6) y (7)]}\\\\
                          &= ε                            &&\\text{[por L5]}
\\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable {s t : ℕ → ℝ} {a b c : ℝ}

def limite (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(u + v) n - (a + b)| < ε
  have hε2 : 0 < ε / 2 := half_pos hε
  cases' hu (ε / 2) hε2 with Nu hNu
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), n ≥ Nu → |u n - a| < ε / 2
  cases' hv (ε / 2) hε2 with Nv hNv
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), n ≥ Nv → |v n - b| < ε / 2
  clear hu hv hε2 hε
  let N := max Nu Nv
  use N
  -- ⊢ ∀ (n : ℕ), n ≥ N → |(s + t) n - (a + b)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have nNu : n ≥ Nu := le_of_max_le_left hn
  specialize hNu n nNu
  -- hNu : |u n - a| < ε / 2
  have nNv : n ≥ Nv := le_of_max_le_right hn
  specialize hNv n nNv
  -- hNv : |v n - b| < ε / 2
  clear hn nNu nNv
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  := rfl
     _ = |(u n - a) + (v n - b)|  := by { congr; ring }
     _ ≤ |u n - a| + |v n - b|    := by apply abs_add
     _ < ε / 2 + ε / 2            := by linarith [hNu, hNv]
     _ = ε                        := by apply add_halves

-- 2ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε hε
  cases' hu (ε/2) (by linarith) with Nu hNu
  cases' hv (ε/2) (by linarith) with Nv hNv
  use max Nu Nv
  intros n hn
  have hn₁ : n ≥ Nu := le_of_max_le_left hn
  specialize hNu n hn₁
  have hn₂ : n ≥ Nv := le_of_max_le_right hn
  specialize hNv n hn₂
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  := by rfl
     _ = |(u n - a) + (v n -  b)| := by {congr; ring}
     _ ≤ |u n - a| + |v n -  b|   := by apply abs_add
     _ < ε / 2 + ε / 2            := by linarith
     _ = ε                        := by apply add_halves

-- 3ª demostración
-- ===============

lemma max_ge_iff
  {α : Type _}
  [LinearOrder α]
  {p q r : α}
  : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε hε
  cases' hu (ε/2) (by linarith) with Nu hNu
  cases' hv (ε/2) (by linarith) with Nv hNv
  use max Nu Nv
  intros n hn
  cases' max_ge_iff.mp hn with hn₁ hn₂
  have cota₁ : |u n - a| < ε/2 := hNu n hn₁
  have cota₂ : |v n - b| < ε/2 := hNv n hn₂
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)| := by rfl
     _ = |(u n - a) + (v n - b)| := by { congr; ring }
     _ ≤ |u n - a| + |v n - b|   := by apply abs_add
     _ < ε                       := by linarith

-- 4ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε hε
  cases' hu (ε/2) (by linarith) with Nu hNu
  cases' hv (ε/2) (by linarith) with Nv hNv
  use max Nu Nv
  intros n hn
  cases' max_ge_iff.mp hn with hn₁ hn₂
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   := by rfl
     _ = |(u n - a) + (v n - b)| := by { congr; ring }
     _ ≤ |u n - a| + |v n - b|   := by apply abs_add
     _ < ε/2 + ε/2               := add_lt_add (hNu n hn₁) (hNv n hn₂)
     _ = ε                       := by simp

-- 5ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε hε
  cases' hu (ε/2) (by linarith) with Nu hNu
  cases' hv (ε/2) (by linarith) with Nv hNv
  use max Nu Nv
  intros n hn
  rw [max_ge_iff] at hn
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   := by rfl
     _ = |(u n - a) + (v n - b)| := by { congr; ring }
     _ ≤ |u n - a| + |v n - b|   := by apply abs_add
     _ < ε                       := by linarith [hNu n (by linarith), hNv n (by linarith)]

-- 6ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
by
  intros ε Hε
  cases' hu (ε/2) (by linarith) with L HL
  cases' hv (ε/2) (by linarith) with M HM
  set N := max L M with _hN
  use N
  have HLN : N ≥ L := le_max_left _ _
  have HMN : N ≥ M := le_max_right _ _
  intros n Hn
  have H3 : |u n - a| < ε/2 := HL n (by linarith)
  have H4 : |v n - b| < ε/2 := HM n (by linarith)
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|   := by rfl
     _ = |(u n - a) + (v n - b)|   := by {congr; ring }
     _ ≤ |(u n - a)| + |(v n - b)| := by apply abs_add
     _ < ε/2 + ε/2                 := by linarith
     _ = ε                         := by ring

-- Lemas usados
-- ============

-- variable (d : ℝ)
-- #check (abs_add a b : |a + b| ≤ |a| + |b|)
-- #check (add_halves a : a / 2 + a / 2 = a)
-- #check (add_lt_add : a < b → c < d → a + c < b + d)
-- #check (half_pos : a > 0 → a / 2 > 0)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (le_of_max_le_left : max a b ≤ c → a ≤ c)
-- #check (le_of_max_le_right : max a b ≤ c → b ≤ c)
-- #check (max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c)
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Convergencia_de_la_suma.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Convergencia_de_la_suma
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma
  assumes "limite u a"
          "limite v b"
  shows   "limite (λ n. u n + v n) (a + b)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦(u n + v n) - (a + b)¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    then have "0 < ε/2"
      by simp
    then have "∃k. ∀n≥k. ¦u n - a¦ < ε/2"
      using assms(1) limite_def by blast
    then obtain Nu where hNu : "∀n≥Nu. ¦u n - a¦ < ε/2"
      by (rule exE)
    then have "∃k. ∀n≥k. ¦v n - b¦ < ε/2"
      using ‹0 < ε/2› assms(2) limite_def by blast
    then obtain Nv where hNv : "∀n≥Nv. ¦v n - b¦ < ε/2"
      by (rule exE)
    have "∀n≥max Nu Nv. ¦(u n + v n) - (a + b)¦ < ε"
    proof (intro allI impI)
      fix n :: nat
      assume "n ≥ max Nu Nv"
      have "¦(u n + v n) - (a + b)¦ = ¦(u n - a) + (v n - b)¦"
        by simp
      also have "… ≤ ¦u n - a¦ + ¦v n - b¦"
        by simp
      also have "… < ε/2 + ε/2"
        using hNu hNv ‹max Nu Nv ≤ n› by fastforce
      finally show "¦(u n + v n) - (a + b)¦ < ε"
        by simp
    qed
    then show "∃k. ∀n≥k. ¦u n + v n - (a + b)¦ < ε "
      by (rule exI)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "limite u a"
          "limite v b"
  shows   "limite (λ n. u n + v n) (a + b)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦(u n + v n) - (a + b)¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    then have "0 < ε/2" by simp
    obtain Nu where hNu : "∀n≥Nu. ¦u n - a¦ < ε/2"
      using ‹0 < ε/2› assms(1) limite_def by blast
    obtain Nv where hNv : "∀n≥Nv. ¦v n - b¦ < ε/2"
      using ‹0 < ε/2› assms(2) limite_def by blast
    have "∀n≥max Nu Nv. ¦(u n + v n) - (a + b)¦ < ε"
      using hNu hNv
      by (smt (verit, ccfv_threshold) field_sum_of_halves max.boundedE)
    then show "∃k. ∀n≥k. ¦u n + v n - (a + b)¦ < ε "
      by blast
  qed
qed

end
</pre>
