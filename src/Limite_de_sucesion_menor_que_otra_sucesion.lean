-- Limite_de_sucesion_menor_que_otra_sucesion.lean
-- Si (∀n)[uₙ ≤ vₙ], entonces lim uₙ ≤ lim vₙ
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a límite de la sucesión u, por
--    def limite (u : ℕ → ℝ) (c : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| < ε
--
-- Demostrar que si (∀ n)[uₙ ≤ vₙ], a es límite de uₙ y c es límite de vₙ,
-- entonces a ≤ c.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por reduccion al absurdo. Supongamos que a ≰ c. Entonces,
--    c < a                                                          (1)
-- Sea
--    ε = (a - c)/2                                                  (2)
-- Por (1),
--    ε > 0.
-- Por tanto, puesto que a es límite de uₙ, existe un p ∈ ℕ tal que
--    (∀ n)[n ≥ p → |uₙ - a| < ε]                                    (3)
-- Análogamente, puesto que c es límite de vₙ, existe un q ∈ ℕ tal
-- que
--    (∀ n)[n ≥ q → |vₙ - c| < ε]                                    (4)
-- Sea
--    k = max(p, q)
-- Entonces, k ≥ p y, por (3),
--   |uₖ - a| < ε                                                    (5)
-- Análogamente, k ≥ q y, por (4),
--   |vₖ - c| < ε                                                    (6)
-- Además, por la hipótesis,
--   uₖ ≤ vₖ                                                         (7)
-- Por tanto,
--    a - c = (a - uₖ) + (uₖ - c)
--          ≤ (a - uₖ) + (vₖ - c)      [por (7)]
--          ≤ |(a - uₖ) + (vₖ - c)|
--          ≤ |a - uₖ| + |vₖ - c|
--          = |uₖ - a| + |vₖ - c|
--          < ε + ε                    [por (5) y (6)]
--          = a - c                    [por (2)]
-- Luego,
--    a - c < a - c
-- que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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
  have _hca : c < a := not_le.mp h
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
  have _hca : c < a := not_le.mp h
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
       _ = a - c                   := by simp [hε]
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
