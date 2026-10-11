-- Reto_17.lean
-- Las sucesiones convergentes están acotadas.
-- Sevilla, 30-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión aₙ es convergente, entonces
-- aₙ está acotada; es decir, existe un M ∈ ℝ tal que para
-- todo n ∈ ℕ, |aₙ| ≤ M.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- La demostración se basa en los siguientes lemas:
-- + Lema 1: Si aₙ converge a L, entonces existe un k ∈ ℕ tal
--   que para todo n ≥ k, |a n| < |L| + 1.
-- + Lema 2: Para cada k ∈ ℕ, existe un M ∈ ℝ tal que para
--   todo i < k, |a i| ≤ M.
--
-- En efecto, por la convergencia de aₙ, existe un L ∈ ℝ tal que
-- aₙ converge a L y, por el Lema 1, existe un k ∈ ℕ tal que
--   ∀ n ≥ k, |aₙ| < |L| + 1                                   (1)
-- Además, por el Lema 2, existe un C ∈ ℝ tal que
--   ∀ i < k, |aᵢ| ≤ C                                         (2)
-- Sea
--   M = máx(|L| + 1, C)                                       (3)
-- Veamos que para todo n ∈ ℕ, |aₙ| ≤ M. Lo haremos
-- distinguiendo dos casos.
--
-- Caso 1: Supongamos que n < k. Entonces,
--    |aₙ| ≤ C    [por (2)]
--         ≤ M    [por (3)]
--
-- Caso 2: Supongamos que n ≥ k. Entonces,
--    |aₙ| ≤ |L| + 1    [por (1)]
--         ≤ M          [por (3)]
--
-- Falta la demostración de los lemas. Para demostrar el
-- primer lema, puesto que aₙ converge a L, existe un k ∈ ℕ tal
-- que
--    ∀ n ≥ k, |aₙ - L| < 1                                   (4)
-- Veamos que k cumple la condición; es decir,
--    ∀ n ≥ k, |aₙ| < |L| + 1
-- Para ello, sea n ∈ ℕ tal que
--    n ≥ k                                                   (5)
-- Entonces,
--    |aₙ| = |L + (aₙ - L)|
--         ≤ |L| + |aₙ - L|    [por la desigualdad triangular]
--         < |L| + 1           [por (4) y (5)]
--
-- Para demostrar el lema 2, sea
--    M = ∑ i ∈ range k, |aᵢ|                                 (6)
-- es decir,
--    M = |a₀| + |a₁| + ... + |aₖ₋₁|
-- Veamos que M es la cota buscada; es decir,
--    ∀ i < k, |aᵢ| ≤ M
-- Para ello, sea i ∈ ℕ tal que
--    i < k                                                   (7)
-- Entonces, puesto que
--    ∀ i ∈ range k, 0 ≤ |aᵢ|                                 (8)
-- y, por (7),
--    i ∈ range k                                             (9)
-- se tiene que
--    |aᵢ| ≤ ∑ i ∈ range k, |aᵢ|    [por (8) y (9)]
--         = M                      [por (6)]

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

def SucConvergente (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

def SucAcotada (a : ℕ → ℝ) : Prop :=
  ∃ M, ∀ n, |a n| ≤ M

variable (a : ℕ → ℝ)

-- Demostraciones del 1º lema
-- ==========================

-- 1ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1
  use k
  -- ⊢ ∀ n ≥ k, |a n| < |L| + 1
  grind

-- 2ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1
  use k
  -- ⊢ ∀ n ≥ k, |a n| < |L| + 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| < |L| + 1
  grind

-- 3ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1
  exact ⟨k, fun _ _ => by grind⟩

-- 4ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
(h 1 one_pos).imp fun _ _ _ _ => by grind

-- 5ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1
  use k
  -- ⊢ ∀ n ≥ k, |a n| < |L| + 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| < |L| + 1
  calc |a n|
       = |L + (a n - L)| := by grind
     _ ≤ |L| + |a n - L| := by grind
     _ < |L| + 1         := by grind

-- 6ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1
  use k
  -- ⊢ ∀ n ≥ k, |a n| < |L| + 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| < |L| + 1
  calc |a n|
       = |L + (a n - L)| := by congr ; ring
     _ ≤ |L| + |a n - L| := by simp only [abs_add_le]
     _ < |L| + 1         := add_lt_add_right (hk n hn) |L|

-- 7ª demostración
-- ---------------

example
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 1
  use k
  -- ⊢ ∀ n ≥ k, |a n| < |L| + 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| < |L| + 1
  calc |a n|
       = |L + (a n - L)| := congrArg abs (add_sub_cancel L (a n)).symm
     _ ≤ |L| + |a n - L| := abs_add_le L (a n - L)
     _ < |L| + 1         := add_lt_add_right (hk n hn) |L|

-- 8ª demostración
-- ---------------

lemma L1
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
  (h 1 one_pos).imp fun _k hk n hn =>
    -- _k : ℕ
    -- hk : ∀ n ≥ _k, |a n - L| < 1
    -- n : ℕ
    -- hn : n ≥ _k
    -- ⊢ |a n| < |L| + 1
    calc |a n|
        = |L + (a n - L)| := congrArg abs (add_sub_cancel L (a n)).symm
      _ ≤ |L| + |a n - L| := abs_add_le L (a n - L)
      _ < |L| + 1         := add_lt_add_right (hk n hn) |L|

-- Demostraciones del 2º lema
-- ==========================

-- 1ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  induction k with
  | zero =>
    -- ⊢ ∃ M, ∀ i < 0, |a i| ≤ M
    use 1
    -- ⊢ ∀ i < 0, |a i| ≤ 1
    grind
  | succ k ih =>
    -- k : ℕ
    -- ih : ∃ M, ∀ i < k, |a i| ≤ M
    -- ⊢ ∃ M, ∀ i < k + 1, |a i| ≤ M
    obtain ⟨M₁, hM₁⟩ := ih
    -- M₁ : ℝ
    -- hM₁ : ∀ i < k, |a i| ≤ M₁
    set M := max M₁ |a k|
    use M
    -- ⊢ ∀ i < k + 1, |a i| ≤ M
    intro i hi
    -- i : ℕ
    -- hi : i < k + 1
    -- ⊢ |a i| ≤ M
    rcases lt_or_ge i k with hi1 | hi2
    · -- hi1 : i < k
      calc |a i|
           ≤ M₁    := by grind
         _ ≤ M     := by grind
    · -- hi2 : k ≤ i
      have h1 : i = k := by grind
      calc |a i|
           = |a k| := by grind
         _ ≤ M     := by grind

-- 2ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  induction k with
  | zero =>
    -- ⊢ ∃ M, ∀ i < 0, |a i| ≤ M
    use 1
    -- ⊢ ∀ i < 0, |a i| ≤ 1
    grind
  | succ k ih =>
    -- k : ℕ
    -- ih : ∃ M, ∀ i < k, |a i| ≤ M
    -- ⊢ ∃ M, ∀ i < k + 1, |a i| ≤ M
    obtain ⟨M₁, hM₁⟩ := ih
    -- M₁ : ℝ
    -- hM₁ : ∀ i < k, |a i| ≤ M₁
    set M := max M₁ |a k|
    use M
    -- ⊢ ∀ i < k + 1, |a i| ≤ M
    intro i hi
    -- i : ℕ
    -- hi : i < k + 1
    -- ⊢ |a i| ≤ M
    rcases lt_or_ge i k with hi1 | hi2
    · -- hi1 : i < k
      calc |a i|
           ≤ M₁    := hM₁ i hi1
         _ ≤ M     := le_max_left _ _
    · -- hi2 : k ≤ i
      have h1 : i = k := Nat.eq_of_le_of_lt_succ hi2 hi
      calc |a i|
           = |a k| := congrArg (|a ·|) h1
         _ ≤ M     := le_max_right _ _

-- 3ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  set M := ∑ i ∈ range k, |a i|
  use M
  -- ⊢ ∀ i < k, |a i| ≤ M
  intro i hi
  -- i : ℕ
  -- hi : i < k
  -- ⊢ |a i| ≤ M
  have h1 : ∀ i ∈ range k, 0 ≤ |a i| := by grind
  grind [single_le_sum]

-- 4ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  set M := ∑ i ∈ range k, |a i|
  use M
  -- ⊢ ∀ i < k, |a i| ≤ M
  intro i hi
  -- i : ℕ
  -- hi : i < k
  -- ⊢ |a i| ≤ M
  have h1 : ∀ i ∈ range k, 0 ≤ |a i| := by
    intro j hj
    exact abs_nonneg (a j)
  exact single_le_sum h1 (mem_range.mpr hi)

-- 5ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  set M := ∑ i ∈ range k, |a i|
  use M
  -- ⊢ ∀ i < k, |a i| ≤ M
  intro i hi
  -- i : ℕ
  -- hi : i < k
  -- ⊢ |a i| ≤ M
  have h1 : ∀ i ∈ range k, 0 ≤ |a i| :=
    fun j _ => abs_nonneg (a j)
  exact single_le_sum h1 (mem_range.mpr hi)

-- 6ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  set M := ∑ i ∈ range k, |a i|
  use M
  -- ⊢ ∀ i < k, |a i| ≤ M
  intro i hi
  -- i : ℕ
  -- hi : i < k
  -- ⊢ |a i| ≤ M
  exact single_le_sum
          (fun j _ => abs_nonneg (a j))
          (mem_range.mpr hi)

-- 7ª demostración
-- ---------------

example
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
by
  set M := ∑ i ∈ range k, |a i|
  use M
  -- ⊢ ∀ i < k, |a i| ≤ M
  exact fun i hi => single_le_sum
                      (fun j _ => abs_nonneg (a j))
                      (mem_range.mpr hi)

-- 8ª demostración
-- ---------------

lemma L2
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
  ⟨∑ i ∈ range k, |a i|,
   fun _ hi => single_le_sum
                 (fun j _ => abs_nonneg (a j))
                 (mem_range.mpr hi)⟩

-- Demostraciones del ejercicio
-- ============================

example
  (ha : SucConvergente a) :
  SucAcotada a :=
by
  obtain ⟨L, hL⟩ := ha
  -- L : ℝ
  -- hL : LimSuc a L
  obtain ⟨k, hk⟩ := L1 a hL
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n| < |L| + 1
  obtain ⟨C, hC⟩ := L2 a k
  -- C : ℝ
  -- hC : ∀ i < k, |a i| ≤ C
  set M := max (|L| + 1) C with hM
  -- hM : M = max (|L| + 1) C
  use M
  -- ⊢ ∀ (n : ℕ), |a n| ≤ M
  intro n
  -- n : ℕ
  -- ⊢ |a n| ≤ M
  rcases lt_or_ge n k with hn1 | hn2
  · -- hn1 : n < k
    calc |a n|
         ≤ C := hC n hn1
       _ ≤ M := le_max_right _ C
  · -- hn2 : k ≤ n
    calc |a n|
         ≤ |L| + 1 := le_of_lt (hk n hn2)
       _ ≤ M       := le_max_left (|L| + 1) _

-- Lemas usados
-- ============

variable (n m : ℕ)
variable (x y z : ℝ)
variable (f : ℝ → ℝ)
variable (s : Finset ℕ)
#check (Nat.eq_of_le_of_lt_succ : n ≤ m → m < n + 1 → m = n)
#check (abs_add_le x y : |x + y| ≤ |x| + |y|)
#check (abs_nonneg x : 0 ≤ |x|)
#check (add_lt_add_right : y < z → ∀ x, x + y < x + z)
#check (add_sub_cancel x y : x + (y - x) = y)
#check (congrArg f : x = y → f x = f y)
#check (le_max_left x y : x ≤ max x y)
#check (le_max_right x y : y ≤ max x y)
#check (le_of_lt : x < y → x ≤ y)
#check (mem_range : m ∈ range n ↔ m < n)
#check (single_le_sum : (∀ i ∈ s, 0 ≤ a i) → ∀ i : ℕ, i ∈ s → a i ≤ ∑ x ∈ s, a x)
