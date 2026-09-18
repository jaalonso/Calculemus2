-- Reto_18.lean
-- Convergencia del producto de sucesiones convergentes.
-- Sevilla, 7-septiembre-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si la sucesión aₙ converge a L y bₙ converge
-- a M, entonces aₙbₙ converge a LM.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Como aₙ converge a L, existe N₁ tal que si n ≥ N₁,
-- entonces
--    |aₙ − L| < 1
-- Por tanto, para n ≥ N₁
--    |aₙ| = |aₙ − L + L|
--         ≤ |aₙ − L| + |L|
--         < 1 + |L|
-- Definamos
--    C = 1 + |L|
-- Entonces
--    C > 0
-- y, para n ≥ N₁
--    |aₙ| ≤ C
-- Ahora, como aₙ converge a L, existe N₂ tal que si n ≥ N₂,
-- entonces
--    |aₙ − L| < ε/(2(|M| + 1))
-- Por otra parte, como bₙ converge a M, existe N₃ tal que si
-- n ≥ N₃, entonces
--    |bₙ − M| < ε/(2C)
-- Sea
--    N = máx⁡{N₁,N₂,N₃}
-- Si n ≥ N, entonces se cumplen las tres desigualdades
-- anteriores. Ahora estimamos:
--    |aₙbₙ − LM|
-- Sumamos y restamos aₙM:
--    aₙbₙ − LM = aₙbₙ − aₙM + aₙM − LM.
-- Entonces
--    |aₙbₙ − LM| = |aₙ(bₙ − M) + M(aₙ − L)|
-- Por la desigualdad triangular,
--    |aₙbₙ − LM| ≤ |aₙ||bₙ − M| +|M||aₙ − L|
-- Como n ≥ N₁,tenemos
--    |aₙ| ≤ C
-- Luego,
--    |aₙbₙ − LM| ≤ C|bₙ − M| + |M||aₙ − L|
-- Usando las cotas elegidas,
--    C|bₙ − M| < C⋅ε/(2C)
--              = ε/2
-- y
--    |M||aₙ − L| < |M|⋅ε/(2(|M| + 1))
-- Como
--    |M|/(|M| + 1) < 1
-- se sigue que
--    |M|⋅ε/(2(|M| + 1)) < ε/2
-- Por tanto,
--    |aₙbₙ − LM| < ε/2 + ε/2
--                = ε
-- Así, para todo ε > 0 existe N tal que si n ≥ N, entonces
--    |aₙbₙ − LM| < ε
-- Esto prueba que, para todo ε > 0, existe N tal que |aₙbₙ − LM| < ε
-- siempre que n ≥ N, es decir, aₙbₙ converge a LM.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

variable {a b c : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª solución
-- ===========

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hc : ∀ n, c n = a n * b n)
  : LimSuc c (L * M) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |c n - L * M| < ε
  obtain ⟨N₁, hN₁⟩ := ha 1 (by positivity)
  -- N₁ : ℕ
  -- hN₁ : ∀ n ≥ N₁, |a n - L| < 1
  have h1 : ∀ n ≥ N₁, |a n| < 1 + |L| := by grind
  set C := 1 + |L|
  -- h1 : ∀ n ≥ N₁, |a n| < C
  have h2 : C > 0 := by grind
  obtain ⟨N₂, hN₂⟩ := ha (ε / (2 * (|M| + 1))) (by positivity)
  -- N₂ : ℕ
  -- hN₂ : ∀ n ≥ N₂, |a n - L| < ε / (2 * (|M| + 1))
  obtain ⟨N₃, hN₃⟩ := hb (ε / (2 * C)) (by positivity)
  -- N₃ : ℕ
  -- hN₃ : ∀ n ≥ N₃, |b n - M| < ε / (2 * C)
  set N := max N₁ (max N₂ N₃)
  use N
  -- ⊢ ∀ n ≥ N, |c n - L * M| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |c n - L * M| < ε
  have h3 : n ≥ N₁ := by grind
  have h4 : n ≥ N₂ := by grind
  have h5 : n ≥ N₃ := by grind
  have h6 : |a n| < C := by grind
  have h7 : |b n - M| < ε / (2 * C) := by grind
  have h8 : |a n - L| < ε / (2 * (|M| + 1)) := by grind
  have h9 : |M| * (ε / (2 * (|M| + 1))) < ε / 2 := by
              field_simp
              -- ⊢ |M| < |M| + 1
              norm_num
  calc |c n - L * M|
       = |a n * b n - L * M|                             := by grind
     _ = |a n * (b n - M) + M * (a n - L)|               := by grind
     _ ≤ |a n * (b n - M)| + |M * (a n - L)|             := by grind
     _ = |a n| * |b n - M| + |M| * |a n - L|             := by grind
     _ ≤ C * |b n - M| + |M| * |a n - L|                 := by gcongr
     _ < C * (ε / (2 * C)) + |M| * |a n - L|             := by gcongr
     _ ≤ C * (ε / (2 * C)) + |M| * (ε / (2 * (|M| + 1))) := by gcongr
     _ = ε / 2 + |M| * (ε / (2 * (|M| + 1)))             := by grind
     _ < ε / 2 + ε / 2                                   := by grind
     _ = ε                                               := by grind

-- 2ª solución
-- ===========

lemma L1
  (h : LimSuc a L)
  : ∃ k, ∀ n ≥ k, |a n| < 1 + |L| :=
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
       = |(a n - L) + L| := congrArg abs (sub_add_cancel (a n) L).symm
     _ ≤ |a n - L| + |L| := abs_add_le (a n - L) L
     _ < 1 + |L|         := (add_lt_add_iff_right |L|).mpr (hk n hn)

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hc : ∀ n, c n = a n * b n)
  : LimSuc c (L * M) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |c n - L * M| < ε
  obtain ⟨N₁, hN₁⟩ := L1 ha
  -- N₁ : ℕ
  -- hN₁ : ∀ n ≥ N₁, |a n| < 1 + |L|
  set C := 1 + |L| with hC
  -- hC : C = 1 + |L|
  have h2 : C > 0 := by positivity
  obtain ⟨N₂, hN₂⟩ := ha (ε / (2 * (|M| + 1))) (by positivity)
  -- N₂ : ℕ
  -- hN₂ : ∀ n ≥ N₂, |a n - M| < ε / (2 * (|M| + 1))
  obtain ⟨N₃, hN₃⟩ := hb (ε / (2 * C)) (by positivity)
  -- N₃ : ℕ
  -- hN₃ : ∀ n ≥ N₃, |b n - M| < ε / (2 * C)
  set N := max N₁ (max N₂ N₃)
  use N
  -- ⊢ ∀ n ≥ N, |c n - L * M| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |c n - L * M| < ε
  have h3 : n ≥ N₁ := by omega
  have h4 : n ≥ N₂ := by omega
  have h5 : n ≥ N₃ := by omega
  have h6 : |a n| < C := by
    calc |a n|
         < 1 + |L| := hN₁ n h3
       _ = C       := rfl
  have h7 : |b n - M| < ε / (2 * C) := hN₃ n h5
  have h8 : |a n - L| < ε / (2 * (|M| + 1)) := hN₂ n h4
  have h9 : |M| * (ε / (2 * (|M| + 1))) < ε / 2 := by
              field_simp
              -- ⊢ |M| < |M| + 1
              norm_num
  calc |c n - L * M|
       = |a n * b n - L * M| :=
            congrArg (|· - L * M|) (hc n)
     _ = |a n * (b n - M) + M * (a n - L)| :=
            by ring_nf
     _ ≤ |a n * (b n - M)| + |M * (a n - L)| :=
            abs_add_le (a n * (b n - M)) (M * (a n - L))
     _ = |a n| * |b n - M| + |M| * |a n - L| :=
            by simp only [abs_mul]
     _ ≤ C * |b n - M| + |M| * |a n - L| :=
            by gcongr
     _ < C * (ε / (2 * C)) + |M| * |a n - L| :=
            by gcongr
     _ ≤ C * (ε / (2 * C)) + |M| * (ε / (2 * (|M| + 1))) :=
            by gcongr
     _ = ε / 2 + |M| * (ε / (2 * (|M| + 1))) :=
            by field_simp
     _ < ε / 2 + ε / 2 :=
            by gcongr
     _ = ε :=
            add_halves ε
