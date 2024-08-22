-- Convergencia_de_la_suma.lean
-- Si la sucesión u converge a a y la v a b, entonces u+v converge a a+b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si la sucesión u converge a a y la v a b, entonces u+v
-- converge a a+b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos los siguientes lemas
--    (∀ a ∈ ℝ)[a > 0 → a / 2 > 0]                                   (L1)
--    (∀ a, b, c ∈ ℝ)[max(a, b) ≤ c → a ≤ c]                         (L2)
--    (∀ a, b, c ∈ ℝ)[max(a, b) ≤ c → b ≤ c]                         (L3)
--    (∀ a, b ∈ ℝ)[|a + b| ≤ |a| + |b|]                              (L4)
--    (∀ a ∈ ℝ)[a / 2 + a / 2 = a]                                   (L5)
--
-- Tenemos que probar que para todo ε ∈ ℝ, si
--    ε > 0                                                          (1)
-- entonces
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |(u + v)(n) - (a + b)| < ε]           (2)
--
-- Por (1) y el lema L1, se tiene que
--    ε/2 > 0                                                        (3)
-- Por (3) y porque el límite de u es a, se tiene que
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |u(n) - a| < ε/2]
-- Sea N₁ ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ N₁ → |u(n) - a| < ε/2]                            (4)
-- Por (3) y porque el límite de v es b, se tiene que
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |v(n) - b| < ε/2]
-- Sea N₂ ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ N₂ → |v(n) - b| < ε/2]                            (5)
-- Sea N = max(N₁, N₂). Veamos que verifica la condición (1). Para ello,
-- sea n ∈ ℕ tal que n ≥ N. Entonces, n ≥ N₁ (por L2) y n ≥ N₂ (por
-- L3). Por tanto, por las propiedades (4) y (5) se tiene que
--    |u(n) - a| < ε/2                                               (6)
--    |v(n) - b| < ε/2                                               (7)
-- Finalmente,
--    |(u + v)(n) - (a + b)| = |(u(n) + v(n)) - (a + b)|
--                           = |(u(n) - a) + (v(n) - b)|
--                           ≤ |u(n) - a| + |v(n) - b|      [por L4]
--                           < ε / 2 + ε / 2                [por (6) y (7)
--                           = ε                            [por L5]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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
