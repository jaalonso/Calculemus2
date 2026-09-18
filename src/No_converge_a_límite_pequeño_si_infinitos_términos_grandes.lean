-- Reto_8.lean
-- Soluciones del 8º reto (28 de junio de 2026).
-- Sucesiones con infinitos términos grandes no convergen a
--   límites pequeños
-- ----------------------------------------------------------

-- ----------------------------------------------------------
-- Demostrar que una sucesión que posee infinitos términos
-- con valor absoluto superior a 10 no puede converger a un
-- límite cuyo valor absoluto sea menor que 5. Es decir, si
-- la sucesión aₙ verifica que
--    ∀ k, ∃ n ≥ k, |aₙ| > 10
-- entonces aₙ no puede tener un límite cuyo valor absoluto
-- sea menor que 5.
-- ----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Para demostrar la negación, se supone que existe un L ∈ ℝ
-- tal que aₙ converge a L y
--    ∣L∣ < 5,                                             (1)
-- y se llega a una contradicción.
--
-- Por la definición de límite, usando ε = 5 > 0, existe
-- k ∈ ℕ tal que
--    ∀ n ≥ k, ∣aₙ − L∣ < 5                                (2)
--
-- Por hipótesis sobre la sucesión, para ese mismo k existe un
-- n ∈ ℕ tal que se cumplen las siguientes dos relaciones:
--    n ≥ k                                                (3)
--    ∣aₙ∣ > 10                                            (4)
-- De (2) y (3) se tiene que
--    ∣aₙ − L∣ < 5                                         (5)
--
-- Para obtener una contradicción basta probar que 10 < 10,
-- que se demuestra a continuación:
--    10 < ∣aₙ∣              [por (4)]
--       = ∣(aₙ − L) + L∣
--       ≤ ∣aₙ − L∣ + ∣L∣    [por desigualdad triangular]
--       < 5 + 5             [por (5) y (1)]
--       = 10.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

variable {a : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : ∀ k, ∃ n ≥ k, |a n| > 10)
  : ¬ ∃ L, LimSuc a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : LimSuc a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨k, hk⟩ := hL1 5 (by norm_num)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 5
  obtain ⟨n, hn1, hn2⟩ := ha k
  -- n : ℕ
  -- hn1 : n ≥ k
  -- hn2 : |a n| > 10
  grind

-- 2ª demostración
-- ===============

example
  (ha : ∀ k, ∃ n ≥ k, |a n| > 10)
  : ¬ ∃ L, LimSuc a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : LimSuc a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨k, hk⟩ := hL1 5 (by norm_num)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 5
  obtain ⟨n, hn1, hn2⟩ := ha k
  -- n : ℕ
  -- hn1 : n ≥ k
  -- hn2 : |a n| > 10
  apply lt_irrefl (10 : ℝ)
  -- ⊢ 10 < 10
  calc 10 < |a n|        := hn2
     _ = |(a n - L) + L| := by grind
     _ ≤ |a n - L| + |L| := by grind
     _ < 5 + 5           := by grind
     _ = 10              := by grind

-- 3ª demostración
-- ===============

example
  (ha : ∀ k, ∃ n ≥ k, |a n| > 10)
  : ¬ ∃ L, LimSuc a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : LimSuc a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨k, hk⟩ := hL1 5 (by positivity)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < 5
  obtain ⟨n, hn1, hn2⟩ := ha k
  -- n : ℕ
  -- hn1 : n ≥ k
  -- hn2 : |a n| > 10
  apply lt_irrefl (10 : ℝ)
  -- ⊢ 10 < 10
  have h5 : |a n - L| < 5 := hk n hn1
  calc 10 < |a n|         := hn2
     _ = |(a n - L) + L|  := congrArg abs (sub_add_cancel (a n) L).symm
     _ ≤ |a n - L| + |L|  := abs_add_le (a n - L) L
     _ < 5 + 5            := add_lt_add h5 hL2
     _ = 10               := by norm_num

-- Lemas usados
-- ============

variable (a b c d : ℝ)

#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (lt_irrefl a : ¬a < a)
#check (sub_add_cancel a b : (a - b) + b = a)
